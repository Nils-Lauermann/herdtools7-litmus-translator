module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)

    let output_converted (test : T.result) =
      Printf.printf "arch = \"%s\"\nname = \"%s\"\n" (Archs.pp A.arch) test.Test_herd.name.Name.name;
      (* Note: replace below warning with escaping (check that this is sane by looking up TOML format) *)
      List.iter (fun (k, v) -> (if String.contains v '"' then print_endline "Warning: value contains quotes; output might be garbled"); Printf.printf "%s = \"%s\"\n" (String.lowercase_ascii k) v) test.Test_herd.info;
      print_endline "addresses = TODO\n\n[locations]";
      let inits = ref IntMap.empty in
      List.iter (fun (loc, v) -> match loc with | A.Location_reg (proc, reg) -> inits := IntMap.update proc (let app = Printf.sprintf "%s = \"%s\"" (A.pp_reg reg) (A.I.V.pp_v v) in function | None -> Some [app] | Some xs -> Some (app :: xs)) !inits | A.Location_global v2 -> Printf.printf "\"%s\" = \"%s\"\n" (A.I.V.pp_v v2) (A.I.V.pp_v v)) (A.state_to_list test.Test_herd.init_state);
      print_newline ();
      (* IntMap.iter (fun i (proc, code) -> Printf.printf "[thread.%s] note: %d\ninit = TODO\ncode = \"\"\"\n" (Proc.dump proc) i; List.iter (fun (_, instr) -> Printf.printf "    %s\n" (A.dump_instruction instr)) code; print_endline "\"\"\"") test.code_segment; *)
      List.iter (fun (proc, code, _) -> Printf.printf "[thread.%s]\ninit = { %s }\ncode = \"\"\"\n" (Proc.dump proc) (String.concat ", " (IntMap.find proc !inits)); List.iter (fun (_, instr) -> Printf.printf "\t%s\n" (A.dump_instruction instr)) code; print_endline "\"\"\"\n") test.Test_herd.start_points; (* TODO restore labels *)
      print_endline "[final]\nTODO";
  end
