open Printf
open Test_herd

module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)
    module Scalar = A.I.V.Cst.Scalar
    module ScalarSet = Set.Make(Scalar)

    let labels_to_offsets test addr =
      let to_offset = let open BranchTarget in function
        | Lbl label ->
          let target = Label.Map.find label test.program in
          Offset (target - addr)
        | Offset _ as o -> o in
      A.map_labels_base to_offset

    let key_value_str = sprintf "%s = %s"
    let print_key k v = print_endline (key_value_str k v)

    let quote s = sprintf "\"%s\"" (String.escaped s)

    let print_header test addresses =
      print_key "arch" (quote (Archs.pp A.arch));
      print_key "name" (quote test.name.Name.name);
      List.iter (fun (k, v) -> print_key (String.lowercase_ascii k) (quote v)) test.info;
      (* isla-axiomatic docs say addresses can be used as a synonym for symbolic, but this doesn't seem to actually work, so symbolic it is *)
      print_key "symbolic" (addresses |> StringSet.elements |> List.map quote |> String.concat ", " |> sprintf "[%s]")

    let looks_like_branch = let open Scalar in function
      | big when le (Scalar.of_int (1 lsl 32)) big -> false
      | b when equal (shift_right_logical b 26) (Scalar.of_int 0b000101) -> true
      | bcond when equal (shift_right_logical bcond 24) (Scalar.of_int 0b01010100) -> true
      | _ -> false

    exception Unexpected of string

    let pp_v = let open A.I.V in function
      | Var i -> raise (Unexpected (sprintf "Encountered Var: %s\n" (pp_csym i)))
      | Val (Constant.Label (_, label)) -> sprintf "%s:" label
      | Val (Constant.Concrete n) -> Scalar.pp (looks_like_branch n) n (* print branches in hex *)
      | v -> pp_v v

    exception UnknownType of string

    let to_isla_type = function
      | "int8_t" | "uint8_t" -> "uint8_t"
      | "int16_t" | "uint16_t" -> "uint16_t"
      | "int32_t" | "uint32_t" -> "uint32_t"
      | "int64_t" | "uint64_t" -> "uint64_t"
      | t -> raise (UnknownType t)

    let cons_to_list_opt x = function
      | None -> Some [x]
      | Some xs -> Some (x::xs)

    type processed_init =
    {
      branches : ScalarSet.t;
      labels : Label.Set.t;
      addresses : StringSet.t;
      locs : string list;
      inits : string list IntMap.t;
      types : string list;
    }

    let process_init_state test =
      let process_v out = let open A.I.V in function
        | Var i -> raise (Unexpected (sprintf "Encountered Var: %s\n" (pp_csym i))) (* not sure what this is, doesn't trigger anywhere in the tests from HAND *)
        | Val (Constant.Symbolic s) ->
          { out with addresses = StringSet.add (Constant.pp_symbol s) out.addresses }
        | Val (Constant.Label (_, label)) ->
          { out with labels = Label.Set.add label out.labels }
        | Val (Constant.Concrete instr) when looks_like_branch instr ->
          { out with branches = ScalarSet.add instr out.branches }
        | _ -> out in
      let accum loc v out = let out = process_v out v in match loc with
        | A.Location_reg (proc, reg) ->
           let initialiser = key_value_str (A.pp_reg reg) (quote (pp_v v)) in
           { out with inits = IntMap.update proc (cons_to_list_opt initialiser) out.inits }
        | A.Location_global v2 ->
           let out = process_v out v2 in
           let key = quote (pp_v v2) in
           let types = let open TestType in match A.look_type test.type_env loc with
             | Ty type_name -> out.types @ [type_name |> to_isla_type |> quote |> key_value_str key]
             | _ -> out.types in
           let initialiser = key_value_str key (quote (pp_v v)) in
           { out with locs = out.locs @ [initialiser]; types } in
      let empty =
        {
          branches = ScalarSet.empty;
          labels = Label.Set.empty;
          addresses = StringSet.empty;
          locs = [];
          inits = IntMap.empty;
          types = [];
        } in
      A.state_fold accum test.init_state empty

    let print_threads test inits addr_to_labels =
      let print_thread (proc, code, x) =
        print_newline ();
        Option.iter (fun _ -> raise (Unexpected "Encountered a Some")) x; (* what is this? *)
        printf "[thread.%s]\n" (Proc.dump proc);
        print_key "init" (sprintf "{ %s }" (IntMap.find_opt proc inits |> Option.value ~default:[] |> String.concat ", "));
        print_endline "code = \"\"\"";
        let print_labels addr =
          Option.iter (List.iter (printf "%s:\n")) (IntMap.find_opt addr addr_to_labels) in
        let print_instruction (addr, instr) =
          printf "\t%s\n" (A.dump_instruction instr);
          print_labels (A.size_of_ins instr + addr) in
        begin match code with
          | [] -> ()
          | (start_addr, _)::_ -> print_labels start_addr; List.iter print_instruction code
        end;
        print_endline "\"\"\"" in
      List.iter print_thread test.start_points

    let bracket = sprintf "(%s)"

    let rec format_subexpr connective = let open ConstrGen in function
      | Atom atom -> begin match atom with
        | LV (loc, v) -> key_value_str (dump_rloc A.dump_location loc) (pp_v v)
        | LL (loc1, loc2) -> key_value_str (A.pp_location_brk loc1) (A.pp_location_brk loc2)
        | FF f -> Fault.pp_fatom pp_v A.I.FaultType.pp f end
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

    let expect_and_expr = let open ConstrGen in function
      | ForallStates e -> ("unsat", Not e)
      | ExistsState e -> ("sat", e)
      | NotExistsState e -> ("unsat", e)

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
        print_endline "]"

    let print_final test =
      print_newline ();
      print_endline "[final]";
      let (expect, expr) = expect_and_expr test.cond in
      print_key "expect" (sprintf "\"%s\"" expect);
      print_key "assertion" (quote (format_constraint_expr expr))

    let print_converted (test : T.result) =
      let { branches; labels; addresses; locs; inits; types } = process_init_state test in
      print_header test addresses;
      Label.Set.iter (print_selfmodify test branches) labels;
      if locs <> [] then begin
        print_newline ();
        print_endline "[locations]";
        List.iter print_endline locs
      end;
      if types <> [] then begin
        print_newline ();
        print_endline "[types]";
        List.iter print_endline types
      end;
      print_threads test inits (addr_to_labels test);
      print_final test
  end
