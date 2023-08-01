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

    let pp_v = function
      | A.I.V.Var i -> sprintf "Encountered Var: %s\n" (A.I.V.pp_csym i)
      | A.I.V.Val (Constant.Label (_, label)) -> sprintf "%s:" label
      | v -> A.I.V.pp_v v

    (* should really make this return a record at some point *)
    let process_init_state (test : T.result) : StringSet.t * string list * string list IntMap.t * string list =
      let update_cons x = function
        | None -> Some [x]
        | Some xs -> Some (x::xs) in
      let addresses = ref StringSet.empty in
      let process_v = function
        | A.I.V.Var i -> printf "Encountered Var: %s\n" (A.I.V.pp_csym i) (* not sure what this is, doesn't trigger anywhere in the tests from HAND *)
        | A.I.V.Val (Constant.Symbolic s) -> addresses := StringSet.add (Constant.pp_symbol s) !addresses
        | _ -> () in
      let accum loc v (locations, inits, types) = process_v v; match loc with
        | A.Location_reg (proc, reg) ->
           let initialiser = key_value_str (A.pp_reg reg) (quote (pp_v v)) in
           (locations, IntMap.update proc (update_cons initialiser) inits, types)
        | A.Location_global v2 ->
           let key = quote (pp_v v2) in
           let types = let open TestType in match A.look_type test.type_env loc with
             | TestType.Ty type_name -> types @ [key_value_str key (quote type_name)]
             | _ -> types in
           process_v v2;
           let initialiser = key_value_str key (quote (pp_v v)) in
           (locations @ [initialiser], inits, types) in
      let (locs, inits, types) = A.state_fold accum test.init_state ([], IntMap.empty, [])
      in (!addresses, locs, inits, types)

    let print_threads (test : T.result) (inits : string list IntMap.t) (addr_to_label : Label.t IntMap.t) =
      let print_thread (proc, code, x) =
        print_newline ();
        (match x with | Some _ -> print_endline "Encountered a Some" | None -> ());
        printf "[thread.%s]\n" (Proc.dump proc);
        print_key "init" (sprintf "{ %s }" (IntMap.find_opt proc inits |> Option.value ~default:[] |> String.concat ", "));
        print_endline "code = \"\"\"";
        let print_instruction (addr, instr) =
          begin match IntMap.find_opt addr addr_to_label with
            | Some label -> printf "%s:\n" label
            | None -> ()
          end;
          printf "\t%s\n" (A.dump_instruction instr) in
        List.iter print_instruction code; (* TODO restore labels in jump/branch instructions *) (* Also labels at the end of a thread's code *)
        print_endline "\"\"\"" in
      List.iter print_thread test.start_points

    let bracket = sprintf "(%s)"

    let rec format_constraint_expr = let open ConstrGen in function
      | Atom atom -> begin match atom with
        | LV (loc, v) -> key_value_str (dump_rloc A.dump_location loc) (A.I.V.pp_v v)
        | LL (loc1, loc2) -> key_value_str (A.pp_location_brk loc1) (A.pp_location_brk loc2)
        | FF f -> Fault.pp_fatom A.I.V.pp_v A.I.FaultType.pp f end
      | Not expr -> "~" ^ bracket (format_constraint_expr expr)
      | And exprs -> String.concat " & " (List.map (fun expr -> bracket (format_constraint_expr expr)) exprs)
      | Or exprs -> String.concat " | " (List.map (fun expr -> bracket (format_constraint_expr expr)) exprs)
      | Implies (l, r) -> sprintf "(%s) -> (%s)" (format_constraint_expr l) (format_constraint_expr r)

    let expect_and_expr = let open ConstrGen in function
    | ForallStates e -> ("unsat", Not e)
    | ExistsState e -> ("sat", e)
    | NotExistsState e -> ("unsat", e)

    let addr_to_label (test : T.result) =
      Label.Map.fold (Fun.flip IntMap.add) test.program IntMap.empty

    let print_converted (test : T.result) =
      let (addresses, locations, inits, types) = process_init_state test in
      print_header test addresses;
      if locations <> [] then begin
        print_newline ();
        print_endline "[locations]";
        List.iter print_endline locations
      end;
      if types <> [] then begin
        print_newline ();
        print_endline "[types]";
        List.iter print_endline types
      end;
      print_threads test inits (addr_to_label test);
      print_newline ();
      print_endline "[final]";
      let (expect, expr) = expect_and_expr test.cond in
      print_key "expect" (sprintf "\"%s\"" expect);
      print_key "assertion" (quote (format_constraint_expr expr))
  end
