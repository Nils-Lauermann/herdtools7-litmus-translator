open IslaLitmusTest

module Make (A:Arch_herd.S) = struct
  module HerdTest = Test_herd.Make(A)
  module Test = IslaLitmusTest.Make(A)
  open Test
  open IslaLitmusCommon.Make(A)

  let sprintf = Printf.sprintf

  (* Helper functions for robust address handling *)
  let extract_base_name addr_name =
    let s = String.trim addr_name in
    if String.starts_with s ~prefix:"pa_" then
      String.sub s 3 (String.length s - 3)
    else if String.starts_with s ~prefix:"phy_" then
      String.sub s 4 (String.length s - 4)
    else if String.starts_with s ~prefix:"PA(" && String.ends_with s ~suffix:")" then
      let content = String.sub s 3 (String.length s - 4) in
      String.trim content
    else s

  let normalize_physical_address addr_name =
    "pa_" ^ (extract_base_name addr_name)

  let extract_virtual_from_physical addr_name =
    let s = String.trim addr_name in
    if String.starts_with s ~prefix:"pa_" ||
       String.starts_with s ~prefix:"phy_" ||
       (String.starts_with s ~prefix:"PA(" && String.ends_with s ~suffix:")") then
      Some (extract_base_name addr_name)
    else None

  let parse_proc str =
    if str.[0] = 'P' then
      int_of_string_opt (String.sub str 1 (String.length str - 1))
    else
      None

  let process_info info =
    let open Info in
    let quote s = sprintf "\"%s\"" (String.escaped s) in
    let process_key_value test_info (key, value) = match key with
      | "tthm" -> raise (Unsupported "Test uses TTHM key")
      | "variant" -> begin match Fault.Handling.parse value with
        | Some handling -> { test_info with handling }
        | None -> raise (Unexpected ("Unknown value of variant key (precision expected): " ^ quote value))
      end
      | "el0" ->
        let proc_strs = String.split_on_char ',' value in
        let parse_proc str = match parse_proc str with
          | None -> raise (Unexpected ("Failed to parse processor in EL0 list: " ^ quote str))
          | Some proc -> proc in
        let procs = List.map parse_proc proc_strs in
        let el0_threads = List.fold_left (Fun.flip ProcSet.add) test_info.el0_threads procs in
        { test_info with el0_threads }
      | key -> { test_info with other_info = (key, value) :: test_info.other_info } in
    let test_info = List.fold_left process_key_value Info.empty info in
    { test_info with other_info = List.rev test_info.other_info }

  let type_name_to_isla_type = function
    | "int8_t" | "uint8_t" -> Some "uint8_t"
    | "int16_t" | "uint16_t" -> Some "uint16_t"
    | "int32_t" | "uint32_t" -> Some "uint32_t"
    | "int64_t" | "uint64_t" -> Some "uint64_t"
    | _ -> None

  let type_to_isla_type t = let open TestType in match t with
    | Ty type_name -> type_name_to_isla_type type_name
    | _ -> None

  let process_initial_state init_state type_env test vmsa =
    let process_v test v = match v_to_cst v with
      | Constant.Symbolic (Constant.Virtual _ as s) ->
        { test with addresses = StringSet.add (Constant.pp_symbol s) test.addresses }
      | Constant.Label (_, label) ->
        { test with label_constants = Label.Set.add label test.label_constants }
      | Constant.Concrete instr when looks_like_branch instr ->
        { test with branch_constants = ScalarSet.add instr test.branch_constants }
      | _ -> test in
    let accum loc rhs test = let test = process_v test rhs in match loc with
      | A.Location_reg (proc, reg) ->
        let update_thread = function
          | None -> raise (Unexpected ("Initialiser for non-existent thread " ^ Proc.pp proc))
          | Some thread ->
            let open Thread in
            let rhs = v_to_cst rhs in
            let thread = match Desc.of_cst rhs with
              | Some desc ->
                { thread with descs_written = DescSet.add desc thread.descs_written }
              | None -> match rhs with
                | Constant.Symbolic (Constant.System (Constant.PTE, addr)) ->
                  { thread with ptes_accessed = StringSet.add addr thread.ptes_accessed }
                | _ -> thread in
            Some { thread with reset = (reg, rhs)::thread.reset } in
        { test with threads = ProcMap.update proc update_thread test.threads }
      | A.Location_global (A.V.Val (Constant.Symbolic (Constant.Virtual addr)) as lhs) ->
        let test = process_v test lhs in
        let addr = addr.Constant.name in
        let types = let open TestType in match type_to_isla_type (A.look_type type_env loc) with
          | Some t -> StringMap.add addr t test.types
          | None -> test.types in
        begin match rhs with
          | A.V.Val (Constant.Concrete rhs) when vmsa ->
            let page_table_setup =
              let open PageTableSetup in
              { test.page_table_setup with initial_values = StringMap.add addr rhs test.page_table_setup.initial_values } in
            { test with page_table_setup; types }
          | _ when vmsa ->
            raise (Unexpected (sprintf "Virtual address %s initialised to non-scalar value %s" addr (A.V.pp_v rhs)))
          | _ -> { test with locations = (addr, v_to_cst rhs)::test.locations; types }
        end
      | A.Location_global (A.V.Val (Constant.Symbolic (Constant.System (Constant.PTE, vaddr)))) ->
        begin match Desc.of_cst (v_to_cst rhs) with
          | Some desc ->
            let page_table_setup =
              let open PageTableSetup in
              { test.page_table_setup with initial_mappings = StringMap.add vaddr desc test.page_table_setup.initial_mappings } in
            { test with page_table_setup }
          | _ -> raise (Unexpected ("PTE initialised to non-descriptor value " ^ A.V.pp_v rhs))
        end
      | _ -> test in
    A.state_fold accum init_state test

  let default_addresses_to_64_bit test =
    let update_address_type = function
      | Some t -> Some t
      | None -> Some "uint64_t" in
    let accum_address = Fun.flip StringMap.update update_address_type in
    let types = StringSet.fold accum_address test.addresses test.types in
    { test with types }

  let process_threads start_points test =
    let process_thread test (proc, code, fh_code) =
      let thread = match ProcMap.find_opt proc test.threads with
        | None -> raise (Unexpected ("Encountered non-existent thread: " ^ Proc.pp proc))
        | Some thread -> thread in
      let is_el1 = Option.is_none (ProcSet.find_opt proc test.info.Info.el0_threads) in
      let reset_extra = if is_el1 then
        ["\"PSTATE.EL\"", "\"0b01\""]
      else [] in
      let reset_extra = ("VBAR_EL1", sprintf "\"extz(%#x%s, 64)\"" (1 + proc) (if is_el1 then "000" else "400"))::reset_extra in

      (* Compute free registers *)
      let registers_from_reset =
        List.fold_left (fun regs (reg, _) -> RegSet.add reg regs)
          RegSet.empty thread.Thread.reset in

      let extract_regs_from_instr regs instr =
        A.fold_regs (RegSet.add, fun _ x -> x) (regs, ()) instr |> fst in

      let registers_from_instrs =
        List.fold_left extract_regs_from_instr RegSet.empty
          (List.map snd code) in

      let registers_from_fh_code = match fh_code with
        | None -> RegSet.empty
        | Some fh_instrs ->
            List.fold_left extract_regs_from_instr RegSet.empty
              (List.map snd fh_instrs) in

      let all_used_registers =
        RegSet.union registers_from_reset
          (RegSet.union registers_from_instrs registers_from_fh_code) in

      let free_registers =
        List.filter (fun reg -> not (RegSet.mem reg all_used_registers))
          A.allowed_for_symb |> List.rev in

      let open Thread in
      let thread = { thread with instructions = code; reset_extra; fault_handler = fh_code; free_registers } in
      let addr_to_instr = List.fold_left (fun addr_to_instr (addr, instr) -> IntMap.add addr instr addr_to_instr) test.addr_to_instr code in
      { test with threads = ProcMap.add proc thread test.threads; addr_to_instr }
    in
    List.fold_left process_thread test start_points

  let pp_v_for_assertion v = match v_to_cst v with
    | Constant.Concrete n -> Scalar.pp (looks_like_branch n) n
    | v -> pp_v_for_reset v

  let bracket = sprintf "(%s)"

  (* Helper to get next free register *)
  let take_register (free_regs : A.reg list) : (A.reg * A.reg list) =
    match free_regs with
    | [] -> failwith "No free registers available for fault predicates"
    | reg :: remaining -> (reg, remaining)

  (* Process assertion: allocate registers on-demand and format constraint expression *)
  let process_assertion expr test =
    (* Track free registers per processor (mutable map) *)
    let free_regs_by_proc = ref ProcMap.empty in

    (* Initialize with free registers from each thread *)
    let () =
      let init_free_regs proc thread =
        free_regs_by_proc := ProcMap.add proc thread.Thread.free_registers !free_regs_by_proc
      in
      ProcMap.iter init_free_regs test.threads
    in

    (* Collect fault predicates with allocated registers grouped by processor *)
    let fault_predicates_by_proc = ref ProcMap.empty in

    let rec format_subexpr connective = let open ConstrGen in function
      | Atom atom -> begin match atom with
        | LV (loc, v) -> key_value_str (dump_rloc A.dump_location loc) (pp_v_for_assertion v)
        | LL (loc1, loc2) -> key_value_str (A.pp_location_brk loc1) (A.pp_location_brk loc2)
        | FF ((proc, lbl_opt), loc_opt, ft_opt) ->
            (* Allocate predicate register on-demand *)
            let current_free_regs = ProcMap.find proc !free_regs_by_proc in
            let (pred_reg, remaining_free_regs) = take_register current_free_regs in

            (* Update map with remaining free registers *)
            free_regs_by_proc := ProcMap.add proc remaining_free_regs !free_regs_by_proc;

            (* Create fault predicate with allocated register *)
            let fault_info = {
              Test.label = lbl_opt;
              Test.location = Option.map v_to_cst loc_opt;
              Test.fault_type = Option.map A.I.FaultType.pp ft_opt;
              Test.predicate_reg = Some pred_reg;
            } in

            (* Add to processor's fault list *)
            let current_faults = match ProcMap.find_opt proc !fault_predicates_by_proc with
              | None -> []
              | Some faults -> faults in
            fault_predicates_by_proc := ProcMap.add proc (current_faults @ [fault_info]) !fault_predicates_by_proc;

            (* Generate register check in assertion *)
            sprintf "%d:%s = 1" proc (A.pp_reg pred_reg)
        end
      | Not expr -> "~" ^ bracket (format_constraint_expr expr)
      | And exprs ->
        let str = String.concat " & " (List.map (format_subexpr (Some "&")) exprs) in
        begin match connective with
          | Some "&" | None -> str
          | _ -> bracket str
        end
      | Or exprs ->
        let str = String.concat " | " (List.map (format_subexpr (Some "|")) exprs) in
        begin match connective with
          | Some "|" | None -> str
          | _ -> bracket str
        end
      | Implies (l, r) -> sprintf "(%s) -> (%s)" (format_constraint_expr l) (format_constraint_expr r)

    and format_constraint_expr e = format_subexpr None e
    in

    let assertion = format_constraint_expr expr in

    (* Update test with collected fault predicates and remaining free registers *)
    let update_thread proc fault_predicates_list threads =
      let thread = ProcMap.find proc threads in
      let remaining_free_regs = ProcMap.find proc !free_regs_by_proc in
      let updated_thread = { thread with
        Thread.fault_predicates = fault_predicates_list;
        Thread.free_registers = remaining_free_regs
      } in
      ProcMap.add proc updated_thread threads
    in

    let updated_threads = ProcMap.fold update_thread !fault_predicates_by_proc test.threads in
    let test = { test with threads = updated_threads } in

    (test, assertion)

  let process_final cond test =
    let (expect, expr) = let open ConstrGen in match cond with
      | ForallStates e -> (Expect.Unsatisfiable, Not e)
      | ExistsState e -> (Expect.Satisfiable), e
      | NotExistsState e -> (Expect.Unsatisfiable, e) in
    let (test, assertion) = process_assertion expr test in
    let final = let open Final in { expect; assertion } in
    { test with final }

  (* Initialise predicate registers in thread reset state *)
  let initialise_predicate_registers test =
    let update_thread_reset proc thread =
      let open Thread in
      let add_pred_reset fault_info resets =
        match fault_info.Test.predicate_reg with
        | None -> failwith (sprintf "Predicate register not allocated for fault in thread %d" proc)
        | Some pred_reg ->
            let init_val = match fault_info.Test.location with
              | Some loc -> loc  (* Initialise to location address *)
              | None -> Constant.Concrete Scalar.zero in  (* No location check, initialise to 0 *)
            (pred_reg, init_val) :: resets
      in
      let pred_resets = List.fold_right add_pred_reset thread.fault_predicates [] in
      { thread with reset = pred_resets @ thread.reset }
    in
    { test with threads = ProcMap.mapi update_thread_reset test.threads }

  let complete_page_table_setup test =
    let ensure_initialised addr initial_mappings =
      StringMap.update addr (function
        | None -> Some (Desc.Valid (AArch64PteVal.default addr))
        | Some d -> Some d) initial_mappings in
    let open PageTableSetup in
    let initial_mappings = StringSet.fold ensure_initialised test.addresses test.page_table_setup.initial_mappings in
    let add_possible_mappings_from _proc thread =
      let open Thread in
      let for_addr addr =
        let update_set desc = function
          | None -> Some (DescSet.singleton desc)
          | Some set -> Some (DescSet.add desc set) in
        DescSet.fold (fun desc -> StringMap.update addr (update_set desc)) thread.descs_written in
      StringSet.fold for_addr thread.ptes_accessed in
    let possible_mappings = ProcMap.fold add_possible_mappings_from test.threads test.page_table_setup.possible_mappings in
    let physical_addresses =
      let add_desc = function
        | Desc.Invalid -> Fun.id
        | Desc.Valid p -> StringSet.add (get_physical_address p) in
      StringSet.empty
      |> StringMap.fold (fun _lhs -> add_desc) initial_mappings
      |> StringMap.fold (fun _lhs -> DescSet.fold add_desc) possible_mappings
      |> StringMap.fold (fun addr _value -> StringSet.add addr) test.page_table_setup.initial_values in
    { test with page_table_setup = { test.page_table_setup with initial_mappings; possible_mappings; physical_addresses; } }

  let convert_test (herd_test : HerdTest.result) vmsa =
    let open Test_herd in
    let test = Test.empty herd_test.arch herd_test.name.Name.name (List.length herd_test.start_points) in
    let test = { test with Test.info = process_info herd_test.Test_herd.info; labels = herd_test.program } in
    let test = process_initial_state herd_test.init_state herd_test.type_env test vmsa in
    let test = if vmsa then default_addresses_to_64_bit test else test in
    let test = complete_page_table_setup test in
    let test = process_threads herd_test.start_points test in
    let test = process_final herd_test.cond test in
    initialise_predicate_registers test
end