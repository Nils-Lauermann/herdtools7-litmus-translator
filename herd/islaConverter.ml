open Printf
open Test_herd

module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)

    let labels_to_offsets (test : T.result) addr =
      let to_offset = let open BranchTarget in function
        | Lbl label ->
          let target = Label.Map.find label test.program in
          Offset (target - addr)
        | Offset _ as o -> o in
      A.map_labels_base to_offset

    let key_value_str = sprintf "%s = %s"
    let print_key k v = print_endline (key_value_str k v)

    let quote s = sprintf "\"%s\"" (String.escaped s)

    let print_header (test : T.result) (addresses : StringSet.t) =
      print_key "arch" (quote (Archs.pp A.arch));
      print_key "name" (quote test.name.Name.name);
      List.iter (fun (k, v) -> print_key (String.lowercase_ascii k) (quote v)) test.info;
      (* isla-axiomatic docs say addresses can be used as a synonym for symbolic, but this doesn't seem to actually work, so symbolic it is *)
      print_key "symbolic" (addresses |> StringSet.elements |> List.map quote |> String.concat ", " |> sprintf "[%s]")

    let looks_like_branch = function
      | big when big >= 1 lsl 32 -> false
      | b when b lsr 26 = 0b000101 -> true
      | bcond when bcond lsr 24 = 0b01010100 -> true
      | _ -> false

    let pp_v = function
      | A.I.V.Var i -> sprintf "Encountered Var: %s\n" (A.I.V.pp_csym i)
      | A.I.V.Val (Constant.Label (_, label)) -> sprintf "%s:" label
      | A.I.V.Val (Constant.Concrete n) -> let n = A.I.V.Cst.Scalar.to_int n in
        if looks_like_branch n then
          sprintf "%#x" n
        else
          string_of_int n
      | v -> A.I.V.pp_v v

    exception UnknownType of string

    let to_isla_type = function
      | "int8_t" | "uint8_t" -> "uint8_t"
      | "int16_t" | "uint16_t" -> "uint16_t"
      | "int32_t" | "uint32_t" -> "uint32_t"
      | "int64_t" | "uint64_t" -> "uint64_t"
      | t -> raise (UnknownType t)

    (* should really make this return a record at some point *)
    let process_init_state (test : T.result) : IntSet.t * Label.Set.t * StringSet.t * string list * string list IntMap.t * string list =
      let update_cons x = function
        | None -> Some [x]
        | Some xs -> Some (x::xs) in
      let addresses = ref StringSet.empty in
      let labels = ref Label.Set.empty in
      let branches = ref IntSet.empty in
      let process_v = function
        | A.I.V.Var i -> printf "Encountered Var: %s\n" (A.I.V.pp_csym i) (* not sure what this is, doesn't trigger anywhere in the tests from HAND *)
        | A.I.V.Val (Constant.Symbolic s) -> addresses := StringSet.add (Constant.pp_symbol s) !addresses
        | A.I.V.Val (Constant.Label (_, label)) -> labels := Label.Set.add label !labels
        | A.I.V.Val (Constant.Concrete instr) when looks_like_branch (A.I.V.Cst.Scalar.to_int instr) -> branches := IntSet.add (A.I.V.Cst.Scalar.to_int instr) !branches
        | _ -> () in
      let accum loc v (locations, inits, types) = process_v v; match loc with
        | A.Location_reg (proc, reg) ->
           let initialiser = key_value_str (A.pp_reg reg) (quote (pp_v v)) in
           (locations, IntMap.update proc (update_cons initialiser) inits, types)
        | A.Location_global v2 ->
           let key = quote (pp_v v2) in
           let types = let open TestType in match A.look_type test.type_env loc with
             | TestType.Ty type_name -> types @ [type_name |> to_isla_type |> quote |> key_value_str key]
             | _ -> types in
           process_v v2;
           let initialiser = key_value_str key (quote (pp_v v)) in
           (locations @ [initialiser], inits, types) in
      let (locs, inits, types) = A.state_fold accum test.init_state ([], IntMap.empty, [])
      in (!branches, !labels, !addresses, locs, inits, types)

    let print_threads (test : T.result) (inits : string list IntMap.t) (addr_to_labels : Label.t list IntMap.t) =
      let print_thread (proc, code, x) =
        print_newline ();
        (match x with | Some _ -> print_endline "Encountered a Some" | None -> ()); (* what is this? *)
        printf "[thread.%s]\n" (Proc.dump proc);
        print_key "init" (sprintf "{ %s }" (IntMap.find_opt proc inits |> Option.value ~default:[] |> String.concat ", "));
        print_endline "code = \"\"\"";
        let print_label addr =
          match IntMap.find_opt addr addr_to_labels with
            | Some labels -> List.iter (printf "%s:\n") labels
            | None -> () in
        let print_instruction (addr, instr) =
          printf "\t%s\n" (A.dump_instruction instr);
          print_label (A.size_of_ins instr + addr) in
        begin match code with
          | [] -> ()
          | (start_addr, _)::_ -> print_label start_addr; List.iter print_instruction code
        end;
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

    let addr_to_labels (test : T.result) =
      let add_label label = function
        | None -> Some [label]
        | Some labels -> Some (label :: labels) in
      Label.Map.fold (fun label addr out -> IntMap.update addr (add_label label) out) test.program IntMap.empty

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

    let print_converted (test : T.result) =
      let (branches, labels, addresses, locations, inits, types) = process_init_state test in
      print_header test addresses;
      if locations <> [] then begin
        print_newline ();
        print_endline "[locations]";
        List.iter print_endline locations
      end;
      let print_selfmodify label =
        print_newline ();
        print_endline "[[self_modify]]";
        print_key "address" (quote (label ^ ":"));
        print_endline "bytes = 4"; (* assume AArch64 *)
        print_endline "values = [";
        IntSet.iter (printf "  \"%#x\",\n") branches;
        let addr = Label.Map.find label test.program in
        let instr = IntMap.find addr test.code_segment |> snd |> List.hd |> snd in
        printf "  \"%#x\"\n" (instr |> labels_to_offsets test addr |> encoding);
        print_endline "]" in
      Label.Set.iter print_selfmodify labels;
      if types <> [] then begin
        print_newline ();
        print_endline "[types]";
        List.iter print_endline types
      end;
      print_threads test inits (addr_to_labels test);
      print_newline ();
      print_endline "[final]";
      let (expect, expr) = expect_and_expr test.cond in
      print_key "expect" (sprintf "\"%s\"" expect);
      print_key "assertion" (quote (format_constraint_expr expr))
  end
