(* TODO mli file *)

open Printf

module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)

    let key_value_str = sprintf "%s = %s"
    let print_key k v = print_endline (key_value_str k v)

    let quote s = sprintf "\"%s\"" (String.escaped s)

    let print_header (test : T.result) =
      print_key "arch" (quote (Archs.pp A.arch));
      print_key "name" (quote test.Test_herd.name.Name.name);
      List.iter (fun (k, v) -> print_key (String.lowercase_ascii k) (quote v)) test.Test_herd.info;
      print_endline "addresses = TODO"

    let process_init_state (test : T.result) : string list * string list IntMap.t =
      let update_cons x = function
        | None -> Some [x]
        | Some xs -> Some (x::xs) in
      let accum loc v (locations, inits) = match loc with
        | A.Location_reg (proc, reg) ->
           let initialiser = key_value_str (A.pp_reg reg) (A.I.V.pp_v v) in
           (locations, IntMap.update proc (update_cons initialiser) inits)
        | A.Location_global v2 ->
           let initialiser = key_value_str (quote (A.I.V.pp_v v2)) (quote (A.I.V.pp_v v)) in
           (locations @ [initialiser], inits) in
      A.state_fold accum test.Test_herd.init_state ([], IntMap.empty)

    let print_threads (test : T.result) (inits : string list IntMap.t) =
      let print_thread (proc, code, _) =
        print_newline ();
        printf "[thread.%s]\n" (Proc.dump proc);
        print_key "init" (sprintf "{ %s }\n" (String.concat ", " (IntMap.find proc inits)));
        print_endline "code = \"\"\"";
        List.iter (fun (_, instr) -> printf "\t%s\n" (A.dump_instruction instr)) code; (* TODO restore labels *)
        print_endline "\"\"\"" in
      List.iter print_thread test.Test_herd.start_points

    let print_converted (test : T.result) =
      print_header test;
      print_newline ();
      print_endline "[locations]";
      let (locations, inits) = process_init_state test in
      List.iter print_endline locations;
      print_threads test inits;
      print_newline ();
      print_endline "[final]";
      print_endline "TODO"
  end
