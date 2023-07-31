open Printf
open Test_herd

module StringSet = Set.Make(String)

module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)

    let key_value_str = sprintf "%s = %s"
    let print_key k v = print_endline (key_value_str k v)

    let quote s = sprintf "\"%s\"" (String.escaped s)

    let print_header (test : T.result) (addresses : StringSet.t) =
      print_key "arch" (quote (Archs.pp A.arch));
      print_key "name" (quote test.name.Name.name);
      List.iter (fun (k, v) -> print_key (String.lowercase_ascii k) (quote v)) test.info;
      (* isla-axiomatic docs say addresses can be used as a synonym for symbolic, but this doesn't seem to actually work, so symbolic it is *)
      print_key "symbolic" (addresses |> StringSet.elements |> List.map quote |> String.concat ", " |> sprintf "[%s]")

    let process_init_state (test : T.result) : StringSet.t * string list * string list IntMap.t =
      let update_cons x = function
        | None -> Some [x]
        | Some xs -> Some (x::xs) in
      let addresses = ref StringSet.empty in
      let process_v = function
        | A.I.V.Var i -> printf "Encountered Var: %s\n" (A.I.V.pp_csym i) (* not sure what this is, doesn't trigger anywhere in the tests from HAND *)
        | A.I.V.Val (Constant.Symbolic s) -> addresses := StringSet.add (Constant.pp_symbol s) !addresses
        | _ -> () in
      let accum loc v (locations, inits) = process_v v; match loc with
        | A.Location_reg (proc, reg) ->
           let initialiser = key_value_str (A.pp_reg reg) (quote (A.I.V.pp_v v)) in
           (locations, IntMap.update proc (update_cons initialiser) inits)
        | A.Location_global v2 ->
           process_v v2;
           let initialiser = key_value_str (quote (A.I.V.pp_v v2)) (quote (A.I.V.pp_v v)) in
           (locations @ [initialiser], inits) in
      let (locs, inits) = A.state_fold accum test.init_state ([], IntMap.empty)
      in (!addresses, locs, inits)

    let print_threads (test : T.result) (inits : string list IntMap.t) =
      let print_thread (proc, code, _) =
        print_newline ();
        printf "[thread.%s]\n" (Proc.dump proc);
        print_key "init" (sprintf "{ %s }\n" (String.concat ", " (IntMap.find proc inits)));
        print_endline "code = \"\"\"";
        List.iter (fun (_, instr) -> printf "\t%s\n" (A.dump_instruction instr)) code; (* TODO restore labels *)
        print_endline "\"\"\"" in
      List.iter print_thread test.start_points

    let bracket = sprintf "(%s)"

    let rec format_constraint_expr = let open ConstrGen in function
      | Atom atom -> begin match atom with
        | LV (loc, v) -> sprintf "%s = %s" (dump_rloc A.dump_location loc) (A.I.V.pp_v v)
        | LL (loc1, loc2) -> sprintf "%s = %s" (A.pp_location_brk loc1) (A.pp_location_brk loc2)
        | FF f -> Fault.pp_fatom A.I.V.pp_v A.I.FaultType.pp f end
      | Not expr -> "~" ^ bracket (format_constraint_expr expr)
      | And exprs -> String.concat " & " (List.map (fun expr -> bracket (format_constraint_expr expr)) exprs)
      | Or exprs -> String.concat " | " (List.map (fun expr -> bracket (format_constraint_expr expr)) exprs)
      | Implies (l, r) -> sprintf "(%s) -> (%s)" (format_constraint_expr l) (format_constraint_expr r)

    let expect_and_expr = let open ConstrGen in function
    | ForallStates e -> ("unsat", Not e)
    | ExistsState e -> ("sat", e)
    | NotExistsState e -> ("unsat", e)

    let print_converted (test : T.result) =
      let (addresses, locations, inits) = process_init_state test in
      print_header test addresses;
      if locations <> [] then begin
        print_newline ();
        print_endline "[locations]";
        List.iter print_endline locations;
      end;
      print_threads test inits;
      print_newline ();
      print_endline "[final]";
      let (expect, expr) = expect_and_expr test.cond in
      print_key "expect" (sprintf "\"%s\"" expect);
      print_key "assertion" (quote (format_constraint_expr expr))
  end
