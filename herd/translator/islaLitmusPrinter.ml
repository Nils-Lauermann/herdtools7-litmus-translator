open Printf

module Make (A:Arch_herd.S) = struct
  open IslaLitmusCommon.Make(A)
  open IslaLitmusTest.Make(A)

  let key_value_str = sprintf "%s = %s"
  let print_key k v = print_endline (key_value_str k v)

  let quote s = sprintf "\"%s\"" (String.escaped s)

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
        let open Thread in
        begin match thread.instructions with
        | [] -> ()
        | (start_addr, _)::_ as instructions -> print_labels start_addr; List.iter print_instruction instructions
      end;
      let end_label = sprintf "islaconv_%s_end" (A.pp_proc proc) in
      let open Info in
      if test.info.precision = Precision.Fatal then print_endline (end_label ^ ":");
      print_endline "\"\"\"";
      print_newline ();
      printf "[thread.%s.reset]\n" (Proc.dump proc);
      List.iter (fun (reg, cst) -> print_key (to_sail_general_reg reg) (quote (pp_v_for_reset cst))) thread.reset;
      print_newline ();
      List.iter (fun (lhs, rhs) -> print_key lhs rhs) thread.reset_extra;
      print_newline ();
      (* Always add a handler because faults might not explicitly be tracked *)
      (* Might add noise to tests though, maybe add a flag not to do this? *)
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
    let open Final in
    print_key "expect" (sprintf "\"%s\"" (pp_expect_for_assertion final.expect));
    print_key "assertion" (quote final.assertion)

  let print_isla_test test =
    print_header test;
    print_page_table_setup test;
    print_types test.types;
    print_threads test;
    print_final test.final
end