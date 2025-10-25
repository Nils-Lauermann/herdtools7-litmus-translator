open Printf

module Make (A:Arch_herd.S) = struct
  open IslaLitmusCommon.Make(A)
  open IslaLitmusTest.Make(A)

  let key_value_str = sprintf "%s = %s"
  let print_key k v = print_endline (key_value_str k v)

  let quote s = sprintf "\"%s\"" (String.escaped s)

  (* Generate fault label checking assembly *)
  let print_fault_label_check proc fault_index fault_pc_reg_name addr_temp_reg_name label =
    printf "\t// Check if fault occurred at expected label %s\n" label;

    (* Load ELR_EL1 to get the fault PC *)
    printf "\tMRS %s,ELR_EL1\n" fault_pc_reg_name;

    (* Get the address of the expected label using ADRP + ADD *)
    printf "\tADRP %s,%s\n" addr_temp_reg_name label;
    printf "\tADD %s,%s,:lo12:%s\n" addr_temp_reg_name addr_temp_reg_name label;

    (* Compare fault PC with expected label address *)
    printf "\tCMP %s,%s\n" fault_pc_reg_name addr_temp_reg_name;
    printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index

  (* Generate fault location checking assembly *)
  let print_fault_location_check proc fault_index va_temp_reg_name pred_reg_name location =
    printf "\t// Check if fault occurred at expected location %s (with untagging)\n" location;
    printf "\t// Note: %s was initialised to address of %s\n" pred_reg_name location;

    (* Check if FAR_EL1 is valid (ESR_EL1.FnV == 0) *)
    printf "\tMRS %s,ESR_EL1\n" va_temp_reg_name;
    printf "\tTBNZ %s,#10,predicate_failed_%d_%d\n" va_temp_reg_name proc fault_index;

    (* Read FAR_EL1 and untag it (keep bits [55:0]) *)
    printf "\tMRS %s,FAR_EL1\n" va_temp_reg_name;
    printf "\tUBFX %s,%s,#0,#56\n" va_temp_reg_name va_temp_reg_name;

    (* Untag the predicate register (contains expected location address) *)
    printf "\t// Untag expected address in %s\n" pred_reg_name;
    printf "\tUBFX %s,%s,#0,#56\n" pred_reg_name pred_reg_name;

    (* Compare untagged addresses *)
    printf "\tCMP %s,%s\n" va_temp_reg_name pred_reg_name;
    printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index

  (* Generate fault type checking assembly *)
  let print_fault_type_check proc fault_index esr_temp_reg_name fault_type =
    printf "\t// Check if fault type matches %s\n" fault_type;
    printf "\tMRS %s,ESR_EL1\n" esr_temp_reg_name;
    printf "\tLSR %s,%s,#26\n" esr_temp_reg_name esr_temp_reg_name; (* Extract EC field - common to all *)

    begin match fault_type with
    | "UndefinedInstruction" ->
        (* EC = 0b000000 (Unknown reason) *)
        printf "\tCMP %s,#0b000000\n" esr_temp_reg_name;
        printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

    | "SupervisorCall" ->
        (* EC = 0b010101 (SVC instruction execution in AArch64 state) *)
        printf "\tCMP %s,#0b010101\n" esr_temp_reg_name;
        printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

    | fault_type when String.starts_with ~prefix:"PacCheck:" fault_type ->
        (* EC = 0b011100 (PAC failure) *)
        printf "\tCMP %s,#0b011100\n" esr_temp_reg_name;
        printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

    | fault_type when fault_type = "TagCheck" || String.starts_with ~prefix:"MMU:" fault_type ->
        (* Check if it's a Data Abort (EC = 0b100100 or 0b100101) *)
        printf "\tAND %s,%s,#0b111110\n" esr_temp_reg_name esr_temp_reg_name; (* Mask out LSB *)
        printf "\tCMP %s,#0b100100\n" esr_temp_reg_name; (* Check if 0b10010x *)
        printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

        (* Re-read ESR_EL1 and extract DFSC from ISS[5:0] *)
        printf "\tMRS %s,ESR_EL1\n" esr_temp_reg_name;
        printf "\tAND %s,%s,#0b111111\n" esr_temp_reg_name esr_temp_reg_name;

        begin match fault_type with
        | "TagCheck" ->
            (* DFSC = 0b010001 *)
            printf "\tCMP %s,#0b010001\n" esr_temp_reg_name;
            printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

        | fault_type when String.starts_with ~prefix:"MMU:" fault_type ->
            begin match String.sub fault_type 4 (String.length fault_type - 4) with
            | "Translation" ->
                (* DFSC[5:2] = 0b0001 *)
                printf "\tAND %s,%s,#0b111100\n" esr_temp_reg_name esr_temp_reg_name;
                printf "\tCMP %s,#0b000100\n" esr_temp_reg_name;
                printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

            | "AccessFlag" ->
                (* DFSC[5:2] = 0b0010 *)
                printf "\tAND %s,%s,#0b111100\n" esr_temp_reg_name esr_temp_reg_name;
                printf "\tCMP %s,#0b001000\n" esr_temp_reg_name;
                printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

            | "Permission" ->
                (* DFSC[5:2] = 0b0011 *)
                printf "\tAND %s,%s,#0b111100\n" esr_temp_reg_name esr_temp_reg_name;
                printf "\tCMP %s,#0b001100\n" esr_temp_reg_name;
                printf "\tB.NE predicate_failed_%d_%d\n" proc fault_index;

            | _ ->
                printf "\t// Unknown MMU fault type, skipping DFSC check\n";
            end;
        | _ -> ()
        end;

    | _ ->
        printf "\t// Unknown fault type %s, skipping type check\n" fault_type;
    end

  (* Generate fault checking assembly for a single fault predicate *)
  let print_fault_check proc temp_reg1_name temp_reg2_name test fault_index fault_info =
    let open IslaLitmusTest.Make(A) in

    (* Build predicate description *)
    let predicate_parts = [] in
    let predicate_parts = match fault_info.label with
      | Some label -> ("label=" ^ label) :: predicate_parts
      | None -> predicate_parts in
    let predicate_parts = match fault_info.location with
      | Some location -> ("location=" ^ A.V.Cst.pp_v location) :: predicate_parts
      | None -> predicate_parts in
    let predicate_parts = match fault_info.fault_type with
      | Some fault_type -> ("type=" ^ fault_type) :: predicate_parts
      | None -> predicate_parts in
    let predicate_desc = match List.rev predicate_parts with
      | [] -> "any fault (no conditions)"
      | parts -> String.concat ", " parts in

    let pred_reg_name = match fault_info.predicate_reg with
      | Some reg -> A.pp_reg reg
      | None -> failwith (sprintf "No predicate register allocated for fault %d in thread %d" fault_index proc) in

    printf "\t// === FAULT PREDICATE %d ===\n" fault_index;
    printf "\t// Predicate: %s\n" predicate_desc;
    printf "\t// Will set %s = 1 if conditions match\n" pred_reg_name;
    printf "\t// =========================\n";

    (* Start with Z flag set (all conditions true) *)
    printf "\tCMP XZR,XZR\n";
    printf "\n";

    (* Check label if specified *)
    begin match fault_info.label with
    | Some label ->
        print_fault_label_check proc fault_index temp_reg1_name temp_reg2_name label;
    | None ->
        printf "\t// No label check required\n"
    end;
    printf "\n";

    (* Check location if specified *)
    begin match fault_info.location with
    | Some location ->
        print_fault_location_check proc fault_index temp_reg1_name pred_reg_name (A.V.Cst.pp_v location);
    | None ->
        printf "\t// No location check required\n"
    end;
    printf "\n";

    (* Check fault type if specified *)
    begin match fault_info.fault_type with
    | Some fault_type ->
        print_fault_type_check proc fault_index temp_reg2_name fault_type;
    | None ->
        printf "\t// No fault type check required\n"
    end;
    printf "\n";

    (* If we reach here, all conditions are satisfied - set predicate register to 1 *)
    printf "\t// All fault predicate conditions satisfied, set predicate register to 1\n";
    printf "\tMOV %s,#1\n" pred_reg_name;
    printf "\n";

    (* Label for when predicate conditions are not satisfied *)
    printf "predicate_failed_%d_%d:\n" proc fault_index

  (* Generate all fault predicate checking code for a thread *)
  let print_fault_predicate_section proc test thread =
    let open IslaLitmusTest.Make(A) in
    let fault_predicates = thread.Thread.fault_predicates in
    if List.length fault_predicates > 0 then begin
      (* Allocate 2 temporary registers from free registers for condition checking *)
      let temp_reg1, temp_reg2 = match thread.Thread.free_registers with
        | r1 :: r2 :: _ -> (A.pp_reg r1, A.pp_reg r2)
        | _ -> failwith (sprintf "Thread %d needs at least 2 free registers for fault predicate checking" proc) in

      (* Big section marker comment *)
      printf "\t// ===== FAULT PREDICATE CHECKING SECTION =====\n";
      printf "\t// Thread %d: Checking %d fault predicates\n" proc (List.length fault_predicates);
      printf "\t// Using temporary registers: %s, %s\n" temp_reg1 temp_reg2;
      printf "\n";

      List.iteri (print_fault_check proc temp_reg1 temp_reg2 test) fault_predicates;

      printf "\t// ========= END FAULT PREDICATE SECTION =========\n";
    end

  let pp_desc_for_page_table_setup = let open AArch64PteVal in function
    | Desc.Invalid -> "invalid"
    | Desc.Valid p when p.dbm <> 0 -> raise (Unsupported "dbm not 0 in page table entry")
    | Desc.Valid p ->
      let attrs = if p.af = 1 then [] else ["AF = 0"] in
      let attrs = if (p.db, p.el0) = (1, 1) then attrs else
        ("AP = 0b" ^ string_of_int p.db ^ string_of_int p.el0)::attrs in
      let out = "pa_" ^ get_physical_address p in
      match attrs with
        | [] -> out
        | _ -> out ^ Printf.sprintf " with [%s]" (String.concat ", " attrs)

  let pp_expect_for_assertion = function
    | Expect.Satisfiable -> "sat"
    | Expect.Unsatisfiable -> "unsat"

  let to_sail_general_reg reg =
    let xreg = A.pp_reg reg in
    if xreg.[0] <> 'X' then
      failwith "to_sail_general_reg: not general-purpose register"
    else
      "R" ^ String.sub xreg 1 (String.length xreg - 1)

      let pp_v_for_init = function
      | Constant.Label (_, label) -> sprintf "%s:" label
      | Constant.Concrete n -> Scalar.pp (looks_like_branch n) n (* print branches in hex *)
      | v -> A.V.Cst.pp_v v

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

  let print_selfmodify test =
    let for_label label =
      print_newline ();
      print_endline "[[self_modify]]";
      print_key "address" (quote (label ^ ":"));
      print_endline "bytes = 4"; (* assume AArch64 *)
      print_endline "values = [";
      ScalarSet.iter (fun branch -> Scalar.pp true branch |> printf "  \"%s\",\n") test.branch_constants;
      let addr = Label.Map.find label test.labels in
      (* IntMap.find addr test.code_segment |> snd |> List.hd |> snd *)
      let instr = IntMap.find addr test.addr_to_instr in
      let to_offset = let open BranchTarget in function
        | Lbl label ->
          let target = Label.Map.find label test.labels in
          Offset (target - addr)
        | Offset _ as o -> o in
      let instr = A.map_labels_base to_offset instr in
      printf "  \"%#x\"\n" (encoding instr);
      print_endline "]" in
    Label.Set.iter for_label test.label_constants

  let print_locations locations =
    if locations <> [] then begin
      print_newline ();
      print_endline "[locations]";
      List.iter (fun (addr, v) -> print_key (quote addr) (quote (A.V.Cst.pp_v v))) locations
    end

  let print_types types =
    if not (StringMap.is_empty types) then begin
      print_newline ();
      print_endline "[types]";
      StringMap.iter (fun k v -> print_endline (key_value_str (quote k) (quote v))) types
    end

  let print_header test =
    print_key "arch" (quote (Archs.pp test.arch));
    print_key "name" (quote test.name);
    List.iter (fun (key, value) -> print_key (String.lowercase_ascii key) (quote value)) test.info.Info.other_info;
    print_key "symbolic" (test.addresses |> StringSet.elements |> List.map quote |> String.concat ", " |> sprintf "[%s]")

  let print_page_table_setup test =
    print_newline ();
    print_endline "page_table_setup = \"\"\"";
    let page_table_setup = test.page_table_setup in
    let open PageTableSetup in
    if not (StringSet.is_empty page_table_setup.physical_addresses) then printf "\tphysical %s;\n" begin
      page_table_setup.physical_addresses
      |> StringSet.elements
      |> List.map ((^) "pa_")
      |> String.concat " "
    end;
    let print_mapping connective addr desc =
      printf "\t%s %s %s;\n" addr connective (pp_desc_for_page_table_setup desc) in
    StringMap.iter (print_mapping "|->") page_table_setup.initial_mappings;
    let print_init addr value =
      printf "\t*pa_%s = %s;\n" addr (Scalar.pp false value) in
    StringMap.iter print_init page_table_setup.initial_values;
    StringMap.iter (fun addr -> DescSet.iter (print_mapping "?->" addr)) page_table_setup.possible_mappings;
    let print_exception_code_page_for proc _code =
      printf "\tidentity %#x000 with code;\n" (1 + proc) in
    ProcMap.iter print_exception_code_page_for test.threads;
    print_endline "\"\"\""

  let print_threads test vmsa =
    let cons_to_list_opt x = function
    | None -> Some [x]
    | Some xs -> Some (x::xs) in
    let addr_to_labels =
      let add_label label addr out = IntMap.update addr (cons_to_list_opt label) out in
      Label.Map.fold add_label test.labels IntMap.empty in
    let print_thread proc thread =
      print_newline ();
      printf "[thread.%d]\n" proc;
      let open Thread in
      if not vmsa then begin
        let pp_init (reg, v) = key_value_str (A.pp_reg reg) (quote (pp_v_for_init v)) in
        print_key "init" (sprintf "{ %s }" (thread.reset |> List.map pp_init |> String.concat ", "))
      end;
      print_endline "code = \"\"\"";
      let print_labels addr =
        Option.iter (List.iter (printf "%s:\n")) (IntMap.find_opt addr addr_to_labels) in
      let print_instruction (addr, instr) =
        printf "\t%s\n" (A.dump_instruction instr);
        print_labels (A.size_of_ins instr + addr) in
        begin match thread.instructions with
        | [] -> ()
        | (start_addr, _)::_ as instructions -> print_labels start_addr; List.iter print_instruction instructions
      end;
      let end_label = sprintf "islaconv_%s_end" (A.pp_proc proc) in
      let open Info in
      if test.info.handling = Fault.Handling.Fatal then print_endline (end_label ^ ":");
      print_endline "\"\"\"";
      if vmsa then begin
        print_newline ();
        printf "[thread.%s.reset]\n" (Proc.dump proc);
        List.iter (fun (reg, cst) -> print_key (to_sail_general_reg reg) (quote (pp_v_for_reset cst))) thread.reset;
        print_newline ();
        List.iter (fun (lhs, rhs) -> print_key lhs rhs) thread.reset_extra;
        print_newline ();
      end;
      (* Print fault handler section if needed *)
      let has_fault_predicates = List.length thread.Thread.fault_predicates > 0 in
      let has_explicit_handler = Option.is_some thread.Thread.fault_handler in

      if has_fault_predicates || has_explicit_handler || vmsa then begin
        print_newline ();
        printf "[section.thread%d_el1_handler]\n" proc;
        let offset = if Option.is_some (ProcSet.find_opt proc test.info.el0_threads) then "400" else "000" in
        print_key "address" (sprintf "\"%#x%s\"" (1 + proc) offset);
        print_endline "code = \"\"\"";

        (* Always prepend fault predicate checking if there are any *)
        print_fault_predicate_section proc test thread;

        (* Append explicit handler code if it exists *)
        begin match thread.Thread.fault_handler with
          | Some explicit_handler ->
            printf "\t// ===== EXPLICIT HANDLER CODE =====\n";
            begin match explicit_handler with
              | [] -> ()
              | (start_addr, _)::_ as instructions -> print_labels start_addr; List.iter print_instruction instructions
            end;
            printf "\t// ===== END EXPLICIT HANDLER =====\n";
          | None ->
            (* No explicit handler *)
            if vmsa then begin
              let handler_temp_reg_name = match thread.Thread.free_registers with
                | reg :: _ -> A.pp_reg reg
                | [] -> failwith "No free register available for default fault handling" in

              begin match test.info.handling with
                | Fault.Handling.Handled ->
                  failwith "Fault.Handling.Handled not yet implemented"
                | Fault.Handling.Fatal ->
                  printf "\t// Fatal fault handling: jump to end label\n";
                  printf "\tADRP %s,%s\n" handler_temp_reg_name end_label;
                  printf "\tADD %s,%s,:lo12:%s\n" handler_temp_reg_name handler_temp_reg_name end_label;
                  printf "\tMSR ELR_EL1,%s\n" handler_temp_reg_name
                | Fault.Handling.Skip ->
                  printf "\t// Skip fault handling: advance PC by 4 bytes\n";
                  printf "\tMRS %s,ELR_EL1\n" handler_temp_reg_name;
                  printf "\tADD %s,%s,#4\n" handler_temp_reg_name handler_temp_reg_name;
                  printf "\tMSR ELR_EL1,%s\n" handler_temp_reg_name
              end;
              printf "\tERET\n";
            end
        end;
        print_endline "\"\"\""
      end in
    ProcMap.iter print_thread test.threads

  let print_final final =
    print_newline ();
    print_endline "[final]";
    let open Final in
    print_key "expect" (sprintf "\"%s\"" (pp_expect_for_assertion final.expect));
    print_key "assertion" (quote final.assertion)

  let print_isla_test test self vmsa =
    print_header test;
    if vmsa then print_page_table_setup test;
    if self then print_selfmodify test;
    print_locations (List.rev test.locations);
    print_types test.types;
    print_threads test vmsa;
    print_final test.final
end