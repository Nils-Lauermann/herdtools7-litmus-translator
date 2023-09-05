open Printf
open Test_herd

module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)
    module Scalar = A.I.V.Cst.Scalar
    module ScalarSet = Set.Make(Scalar)
    module ProcSet = Set.Make(Proc)
    module ProcMap = Map.Make(Proc)

    exception Unexpected of string
    exception Unsupported of string

    let key_value_str = sprintf "%s = %s"
    let print_key k v = print_endline (key_value_str k v)

    let quote s = sprintf "\"%s\"" (String.escaped s)

    let get_physical_address p = match p.AArch64PteVal.oa with
      | OutputAddress.PTE _ -> raise (Unsupported "Output address is PTE (intermediate entry?)")
      | OutputAddress.PHY phys -> phys

    module Desc = struct
      type t =
        | Invalid
        | Valid of AArch64PteVal.t

      let equal lhs rhs = match (lhs, rhs) with
        | (Invalid, Invalid) -> true
        | (Valid lhs, Valid rhs) -> AArch64PteVal.eq lhs rhs
        | _ -> false
      let compare lhs rhs = match (lhs, rhs) with
        | (Invalid, Invalid) -> 0
        | (Invalid, Valid _) -> -1
        | (Valid _, Invalid) -> 1
        | (Valid lhs, Valid rhs) -> AArch64PteVal.compare lhs rhs

      let pp_for_page_table_setup = function
        | Invalid -> "invalid"
        | Valid p when p.dbm <> 0 -> raise (Unsupported "dbm not 0 in page table entry")
        | Valid p ->
          let attrs = if p.af = 1 then [] else ["AF = 0"] in
          let attrs = if (p.db, p.el0) = (1, 1) then attrs else
            ("AP = 0b" ^ string_of_int p.db ^ string_of_int p.el0)::attrs in
          let out = "pa_" ^ get_physical_address p in
          match attrs with
            | [] -> out
            | _ -> out ^ sprintf " with [%s]" (String.concat ", " attrs)
    end

    module DescSet = Set.Make(Desc)

    module PageTableSetup = struct
     type t =
      {
        physical_addresses : StringSet.t;
        initial_mappings : Desc.t StringMap.t;
        possible_mappings : DescSet.t StringMap.t;
        initial_values : Scalar.t StringMap.t;
        threads_with_handlers: ProcSet.t;
      }

      let empty =
        {
          physical_addresses = StringSet.empty;
          initial_mappings = StringMap.empty;
          possible_mappings = StringMap.empty;
          initial_values = StringMap.empty;
          threads_with_handlers = ProcSet.empty;
        }
    end

    module Thread = struct
      type t =
        {
          instructions : (int * A.instruction) list;
          reset : (string * string) list;
          ptes_accessed : StringSet.t;
          descs_written : DescSet.t;
        }

      let empty =
        {
          instructions = [];
          reset = [];
          ptes_accessed = StringSet.empty;
          descs_written = DescSet.empty;
        }
    end

    module Expect = struct
      type t =
        | Satisfiable
        | Unsatisfiable

      let pp_for_assertion = function
        | Satisfiable -> "sat"
        | Unsatisfiable -> "unsat"
    end

    module Final = struct
      type t =
        {
          expect : Expect.t;
          assertion : string;
        }

      let empty = (* this shouldn't really exist *)
        {
          expect = Expect.Satisfiable;
          assertion = "true";
        }
    end

    module TestInfo = struct
      type t =
        {
          precision : Precision.t;
          el0_threads : ProcSet.t;
          other_info : (string * string) list;
        }

      let empty =
        {
          precision = Precision.Handled;
          el0_threads = ProcSet.empty;
          other_info = [];
        }
    end

    type isla_test =
    {
      arch : Archs.t;
      name : string;
      info : TestInfo.t;
      label_constants : Label.Set.t;
      branch_constants : ScalarSet.t;
      addresses : StringSet.t;
      page_table_setup : PageTableSetup.t;
      types : string StringMap.t;
      threads : Thread.t ProcMap.t;
      labels : int Label.Map.t;
      final : Final.t;
    }

    let isla_test_empty arch name num_threads =
      let rec empty_threads i threads =
        if i = num_threads then
          threads
        else
          empty_threads (1 + i) (ProcMap.add i Thread.empty threads) in
      {
        arch = arch;
        name = name;
        info = TestInfo.empty;
        label_constants = Label.Set.empty;
        branch_constants = ScalarSet.empty;
        addresses = StringSet.empty;
        page_table_setup = PageTableSetup.empty;
        types = StringMap.empty;
        threads = empty_threads 0 ProcMap.empty;
        labels = Label.Map.empty;
        final = Final.empty;
      }

    let parse_proc str =
      if str.[0] = 'P' then
        int_of_string_opt (String.sub str 1 (String.length str - 1))
      else
        None

    let process_info info =
      let open TestInfo in
      let process_key_value test_info (key, value) = match key with
        | "tthm" -> raise (Unsupported "Test uses TTHM key")
        | "variant" -> begin match Precision.parse value with
          | Some precision -> { test_info with precision }
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
      let test_info = List.fold_left process_key_value TestInfo.empty info in
      { test_info with other_info = List.rev test_info.other_info }

    let looks_like_branch = let open Scalar in function
      | big when le (Scalar.of_int (1 lsl 32)) big -> false
      | b when equal (shift_right_logical b 26) (Scalar.of_int 0b000101) -> true
      | bcond when equal (shift_right_logical bcond 24) (Scalar.of_int 0b01010100) -> true
      | _ -> false

    (* TODO: unwind the layers of modules to avoid this regrettable hack: *)
    let coerce_pte_val : A.I.V.Cst.PteVal.t -> AArch64PteVal.t = Obj.magic

    type my_v = Label of string
              | Concrete of Scalar.t
              | PTE_Desc of Desc.t
              | PTE_Addr of string
              | Other of A.I.V.v

    let v_to_my_v = let open A.I.V in function
      | Var i -> raise (Unexpected (sprintf "Encountered Var: %s\n" (pp_csym i)))
      | Val (Constant.Label (_, label)) -> Label label
      | Val (Constant.Concrete n) -> Concrete n
      | Val (Constant.PteVal p) ->
        let p = coerce_pte_val p in
        let open AArch64PteVal in
        if (p.db, p.dbm, p.el0) <> (1, 0, 1) then
          raise (Unsupported (sprintf "(db, dbm, el0) = (%d, %d, %d); only (1, 0, 1) is supported" p.db p.dbm p.el0)) (* TODO *)
        else if p.AArch64PteVal.valid = 0 then
          PTE_Desc Desc.Invalid
        else
          PTE_Desc (Desc.Valid p)
      | Val (Constant.Symbolic (Constant.System (Constant.PTE, sym))) -> PTE_Addr sym
      | v -> Other v

    let pp_v_for_reset v = match v_to_my_v v with
      | Label label -> label ^ ":"
      | Concrete n -> sprintf "extz(%s, 64)" (Scalar.pp true n)
      | PTE_Desc Desc.Invalid -> "extz(0x0, 64)"
      | PTE_Desc (Desc.Valid p) ->
        let open AArch64PteVal in
        begin match (p.oa, p.af) with
          | (OutputAddress.PTE _, _) -> raise (Unsupported "PTE no physical address (intermediate?)")
          | (OutputAddress.PHY phys, 0) -> sprintf "bvxor(extz(0x400, 64), mkdesc3(oa=pa_%s))" phys (* TODO *)
          | (OutputAddress.PHY phys, 1) -> sprintf "mkdesc3(oa=pa_%s)" phys
          | (OutputAddress.PHY _, n) -> raise (Unexpected (sprintf "AF (%d) has more than one bit" n))
        end
      | PTE_Addr vaddr -> sprintf "pte3(%s, page_table_base)" vaddr
      | Other v -> A.I.V.pp_v v

    let pp_v_for_assertion = function
      | A.I.V.Val (Constant.Concrete n) -> Scalar.pp (looks_like_branch n) n
      | v -> raise (Unexpected ("Weird value in assertion LV atom: " ^ A.I.V.pp_v v))

    let type_name_to_isla_type = function
      | "int8_t" | "uint8_t" -> Some "uint8_t"
      | "int16_t" | "uint16_t" -> Some "uint16_t"
      | "int32_t" | "uint32_t" -> Some "uint32_t"
      | "int64_t" | "uint64_t" -> Some "uint64_t"
      | _ -> None

    let type_to_isla_type t = let open TestType in match t with
      | Ty type_name -> type_name_to_isla_type type_name
      | _ -> None

    let to_sail_general_reg reg =
      let xreg = A.pp_reg reg in
      if xreg.[0] <> 'X' then
        failwith "to_sail_general_reg: not general-purpose register"
      else
        "R" ^ String.sub xreg 1 (String.length xreg - 1)

    let process_initial_state init_state type_env test =
      let process_v test = let open A.I.V in function
        | Var i -> raise (Unexpected (sprintf "Encountered Var: %s\n" (pp_csym i))) (* not sure what this is, doesn't trigger anywhere in the tests I've tried *)
        | Val (Constant.Symbolic (Constant.Virtual _ as s)) ->
          { test with addresses = StringSet.add (Constant.pp_symbol s) test.addresses }
        | Val (Constant.Label (_, label)) ->
          { test with label_constants = Label.Set.add label test.label_constants }
        | Val (Constant.Concrete instr) when looks_like_branch instr ->
          { test with branch_constants = ScalarSet.add instr test.branch_constants }
        | _ -> test in
      let accum loc rhs test = let test = process_v test rhs in match loc with
        | A.Location_reg (proc, reg) ->
          let initialiser = (to_sail_general_reg reg, (quote (pp_v_for_reset rhs))) in
          let update_thread = function
            | None -> raise (Unexpected ("Initialiser for non-existent thread " ^ Proc.pp proc))
            | Some thread ->
              let open Thread in
              let thread = match v_to_my_v rhs with
                | PTE_Desc desc ->
                  { thread with descs_written = DescSet.add desc thread.descs_written }
                | PTE_Addr addr ->
                  { thread with ptes_accessed = StringSet.add addr thread.ptes_accessed }
                | _ -> thread in
              Some { thread with reset = initialiser::thread.reset } in
          { test with threads = ProcMap.update proc update_thread test.threads }
        | A.Location_global (A.I.V.Val (Constant.Symbolic (Constant.Virtual vaddr)) as lhs) ->
          let test = process_v test lhs in
          let vaddr = vaddr.Constant.name in
          let types = let open TestType in match type_to_isla_type (A.look_type type_env loc) with
            | Some t -> StringMap.add vaddr t test.types
            | None -> test.types in
          begin match rhs with
            | A.I.V.Val (Constant.Concrete rhs) ->
              let page_table_setup =
                let open PageTableSetup in
                { test.page_table_setup with initial_values = StringMap.add vaddr rhs test.page_table_setup.initial_values } in
              { test with page_table_setup; types }
            | _ -> raise (Unexpected (sprintf "Virtual address %s initialised to non-scalar value %s" vaddr (A.I.V.pp_v rhs)))
          end
        | A.Location_global (A.I.V.Val (Constant.Symbolic (Constant.System (Constant.PTE, vaddr)))) ->
          begin match v_to_my_v rhs with
            | PTE_Desc Desc.Invalid ->
              let page_table_setup =
                let open PageTableSetup in
                { test.page_table_setup with initial_mappings = StringMap.add vaddr Desc.Invalid test.page_table_setup.initial_mappings } in
              { test with page_table_setup }
            | PTE_Desc valid_desc ->
              let page_table_setup =
                let open PageTableSetup in
                { test.page_table_setup with initial_mappings = StringMap.add vaddr valid_desc test.page_table_setup.initial_mappings } in
              { test with page_table_setup }
            | _ -> raise (Unexpected ("PTE initialised to non-descriptor value " ^ A.I.V.pp_v rhs))
          end
        | _ -> test in
      A.state_fold accum init_state test

    let process_threads start_points test =
      let process_thread test (proc, code, _) =
        let thread = match ProcMap.find_opt proc test.threads with
          | None -> raise (Unexpected ("Encountered non-existent thread: " ^ Proc.pp proc))
          | Some thread -> thread in
        let is_el1 = Option.is_none (ProcSet.find_opt proc test.info.TestInfo.el0_threads) in
        let open Thread in
        let reset = if is_el1 then
          ("\"PSTATE.EL\"", "\"0b01\"")::thread.reset
        else thread.reset in
        let reset = if Option.is_some (ProcSet.find_opt proc test.page_table_setup.PageTableSetup.threads_with_handlers) then
          let reset = ("R12", "\"extz(0x0, 64)\"")::reset in
          ("VBAR_EL1", sprintf "\"%#x%s\"" (1 + proc) (if is_el1 then "000" else "400"))::reset
        else reset in
        let thread = { thread with instructions = code; reset } in
        { test with threads = ProcMap.add proc thread test.threads }
      in
      List.fold_left process_thread test start_points

    let default_addresses_to_64_bit test = (* todo work on types not test *)
      let update_address_type = function
        | Some t -> Some t
        | None -> Some "uint64_t" in
      let accum_address = Fun.flip StringMap.update update_address_type in
      let types = StringSet.fold accum_address test.addresses test.types in
      { test with types }

    let bracket = sprintf "(%s)"

    let rec format_subexpr connective = let open ConstrGen in function
      | Atom atom -> begin match atom with
        | LV (loc, v) -> key_value_str (dump_rloc A.dump_location loc) (pp_v_for_assertion v)
        | LL (loc1, loc2) -> key_value_str (A.pp_location_brk loc1) (A.pp_location_brk loc2)
        | FF ((proc, Some lbl), _, _) -> key_value_str (string_of_int proc ^ ":X12") (lbl ^ ":")
        | FF _ -> raise (Unsupported "fault without label") end
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

    (*let rec fold_expr f a = let open ConstrGen in function
      | Atom atom -> f a atom
      | Not expr -> fold_expr f a expr
      | And exprs | Or exprs -> List.fold_left (fold_expr f) a exprs
      | Implies (l, r) -> fold_expr f (fold_expr f a l) r

    let addr_to_labels test =
      let add_label label addr out = IntMap.update addr (cons_to_list_opt label) out in
      Label.Map.fold add_label test.program IntMap.empty

    exception Unknown_Self_Modify of string

    let encoding instruction =
      let instruction_str = A.dump_instruction instruction in
      let open String in
      if starts_with ~prefix:"B ." instruction_str then
        let offset_str = sub instruction_str 3 (length instruction_str - 3) in
        0x1400_0000 lor (int_of_string offset_str asr 2)
      else if starts_with ~prefix:"B.EQ ." instruction_str then
        let offset_str = sub instruction_str 6 (length instruction_str - 6) in
        0x5400_0000 lor (int_of_string offset_str lsl 3)
      else
        raise (Unknown_Self_Modify instruction_str)

     let print_selfmodify test branches label =
        print_newline ();
        print_endline "[[self_modify]]";
        print_key "address" (quote (label ^ ":"));
        print_endline "bytes = 4"; (* assume AArch64 *)
        print_endline "values = [";
        ScalarSet.iter (fun branch -> Scalar.pp true branch |> printf "  \"%s\",\n") branches;
        let addr = Label.Map.find label test.program in
        let instr = IntMap.find addr test.code_segment |> snd |> List.hd |> snd in
        printf "  \"%#x\"\n" (instr |> labels_to_offsets test addr |> encoding);
        print_endline "]" *)

    let print_types types =
      if not (StringMap.is_empty types) then begin
        print_newline ();
        print_endline "[types]";
        StringMap.iter (fun k v -> print_endline (key_value_str (quote k) (quote v))) types
      end 

    let process_final cond test =
      let (expect, expr) = let open ConstrGen in let open Expect in match cond with
        | ForallStates e -> (Expect.Unsatisfiable, Not e)
        | ExistsState e -> (Expect.Satisfiable), e
        | NotExistsState e -> (Expect.Unsatisfiable, e) in
      let assertion = format_constraint_expr expr in
      let final = let open Final in { expect; assertion } in
      { test with final }

    (*let find_threads_with_faults test =
      let check_atom threads = function
        | ConstrGen.FF ((proc, _), _, _) -> IntSet.add proc threads
        | _ -> threads in
      fold_expr check_atom IntSet.empty (snd (expect_and_expr (test.cond)))*)

    let complete_page_table_setup test =
      let ensure_initialised addr initial_mappings =
        StringMap.update addr (function
          | None -> Some (Desc.Valid (AArch64PteVal.default addr))
          | Some d -> Some d) initial_mappings in
      let initial_mappings = StringSet.fold ensure_initialised test.addresses test.page_table_setup.initial_mappings in
      let add_possible_mappings_from _proc thread =
        let for_addr addr =
          let update_set desc = function
            | None -> Some (DescSet.singleton desc)
            | Some set -> Some (DescSet.add desc set) in
          DescSet.fold (fun desc -> StringMap.update addr (update_set desc)) thread.Thread.descs_written in
        StringSet.fold for_addr thread.Thread.ptes_accessed in
      let possible_mappings = ProcMap.fold add_possible_mappings_from test.threads test.page_table_setup.possible_mappings in
      let physical_addresses =
        let add_desc = function
          | Desc.Invalid -> Fun.id
          | Desc.Valid p -> StringSet.add (get_physical_address p) in
        StringSet.empty
        |> StringMap.fold (fun _lhs -> add_desc) initial_mappings
        |> StringMap.fold (fun _lhs -> DescSet.fold add_desc) possible_mappings in
      { test with page_table_setup = { test.page_table_setup with initial_mappings; possible_mappings; physical_addresses; } }

    let convert_test (herd_test : T.result) =
      let test = isla_test_empty herd_test.arch herd_test.name.Name.name (List.length herd_test.start_points) in
      let test = { test with info = process_info herd_test.Test_herd.info; labels = herd_test.program } in
      let test = process_initial_state herd_test.init_state herd_test.type_env test in
      let test = default_addresses_to_64_bit test in
      let test = complete_page_table_setup test in
      let test = process_threads herd_test.start_points test in
      process_final herd_test.cond test

    let print_header test =
      print_key "arch" (quote (Archs.pp test.arch));
      print_key "name" (quote test.name);
      List.iter (fun (key, value) -> print_key (String.lowercase_ascii key) (quote value)) test.info.other_info;
      print_key "symbolic" (test.addresses |> StringSet.elements |> List.map quote |> String.concat ", " |> sprintf "[%s]")

    let print_page_table_setup test =
      print_newline ();
      print_endline "page_table_setup = \"\"\"";
      let page_table_setup = test.page_table_setup in
      printf "\tphysical %s;\n" begin
        page_table_setup.PageTableSetup.physical_addresses
        |> StringSet.elements
        |> List.map ((^) "pa_")
        |> String.concat " "
      end;
      let print_mapping connective addr desc =
        printf "\t%s %s %s;\n" addr connective (Desc.pp_for_page_table_setup desc) in
      StringMap.iter (print_mapping "|->") page_table_setup.initial_mappings;
      let print_init addr value =
        printf "\t*%s = %s;\n" addr (Scalar.pp false value) in
      StringMap.iter print_init page_table_setup.initial_values;
      StringMap.iter (fun addr -> DescSet.iter (print_mapping "?->" addr)) page_table_setup.possible_mappings;
      let print_exception_code_page_for proc _code =
        printf "\tidentity %#x000 with code;\n" (1 + proc) in
      ProcMap.iter print_exception_code_page_for test.threads;
      print_endline "\"\"\""

    let print_threads test =
      let cons_to_list_opt x = function
      | None -> Some [x]
      | Some xs -> Some (x::xs) in
      let addr_to_labels =
        let add_label label addr out = IntMap.update addr (cons_to_list_opt label) out in
        Label.Map.fold add_label test.labels IntMap.empty in
      let print_thread proc thread =
        print_newline ();
        printf "[thread.%d]\n" proc;
        print_endline "code = \"\"\"";
        let print_labels addr =
          Option.iter (List.iter (printf "%s:\n")) (IntMap.find_opt addr addr_to_labels) in
        let print_instruction (addr, instr) =
          printf "\t%s\n" (A.dump_instruction instr);
          print_labels (A.size_of_ins instr + addr) in
        begin match thread.Thread.instructions with
          | [] -> ()
          | (start_addr, _)::_ as instructions -> print_labels start_addr; List.iter print_instruction instructions
        end;
        let end_label = sprintf "islaconv_%s_end" (A.pp_proc proc) in
        if test.info.precision = Precision.Fatal then print_endline (end_label ^ ":");
        print_endline "\"\"\"";
        print_newline ();
        printf "[thread.%s.reset]\n" (Proc.dump proc);
        List.iter (fun (lhs, rhs) -> print_key lhs rhs) thread.reset;
        print_newline ();
        printf "[section.thread%d_el1_handler]\n" proc;
        let offset = if Option.is_some (ProcSet.find_opt proc test.info.el0_threads) then "400" else "000" in
        print_key "address" (sprintf "\"%#x%s\"" (1 + proc) offset);
        print_endline "code = \"\"\"";
        print_endline "\tMRS X12,ELR_EL1";
        begin match test.info.precision with
          | Precision.Handled -> ()
          | Precision.Fatal ->
            print_endline ("\tMOV X14," ^ end_label);
            print_endline "\tMSR ELR_EL1,X14"
          | Precision.LoadsFatal -> raise (Unsupported "LoadsFatal precision setting")
          (* LoadsFatal is undocumented and doesn't appear in the tests in catalogue *)
          | Precision.Skip ->
            print_endline "\tMRS X14,ELR_EL1";
            print_endline "\tADD X14,X14,#4";
            print_endline "\tMSR ELR_EL1,X14"
        end;
        print_endline "\tERET";
        print_endline "\"\"\"" in
      ProcMap.iter print_thread test.threads

    let print_final final =
      print_newline ();
      print_endline "[final]";
      print_key "expect" (sprintf "\"%s\"" (Expect.pp_for_assertion final.Final.expect));
      print_key "assertion" (quote final.assertion)

    let print_isla_test test =
      print_header test;
      print_page_table_setup test;
      print_types test.types;
      print_threads test;
      print_final test.final
  end
