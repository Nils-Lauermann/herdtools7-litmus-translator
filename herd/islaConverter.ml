open Printf
open Test_herd

module Make
    (A:Arch_herd.S) =
  struct
    module T = Test_herd.Make(A)
    module Scalar = A.I.V.Cst.Scalar
    module ScalarSet = Set.Make(Scalar)

    exception Unexpected of string
    exception Unsupported of string

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

    type test_info =
    {
      precision : Precision.t;
      el0_threads : IntSet.t;
    }

    let parse_proc str =
      if str.[0] = 'P' then
        int_of_string_opt (String.sub str 1 (String.length str - 1))
      else
        None

    let print_header_and_parse_info test addresses =
      print_key "arch" (quote (Archs.pp A.arch));
      print_key "name" (quote test.name.Name.name);
      let process_info info (key, value) = match String.lowercase_ascii key with
        | "tthm" -> raise (Unsupported "Test uses TTHM key")
        | "variant" -> begin match Precision.parse value with
          | Some precision -> { info with precision }
          | None -> raise (Unexpected ("Unknown value of variant key (precision expected): " ^ quote value))
        end
        | "el0" ->
          let proc_strs = String.split_on_char ',' value in
          let parse_proc str = match parse_proc str with
            | None -> raise (Unexpected ("Failed to parse processor in EL0 list: " ^ quote str))
            | Some proc -> proc in
          let procs = List.map parse_proc proc_strs in
          let el0_threads = List.fold_left (Fun.flip IntSet.add) info.el0_threads procs in
          { info with el0_threads }
        | key -> print_key key (quote value); info in
      (* List.iter (fun (k, v) -> print_key (String.lowercase_ascii k) (quote v)) test.info; *)
      let info_initial = { precision = Precision.Handled; el0_threads = IntSet.empty; } in
      let info = List.fold_left process_info info_initial test.info in
      (* isla-axiomatic docs say addresses can be used as a synonym for symbolic, but this doesn't seem to actually work, so symbolic it is *)
      print_key "symbolic" (addresses |> StringSet.elements |> List.map quote |> String.concat ", " |> sprintf "[%s]");
      info

    let looks_like_branch = let open Scalar in function
      | big when le (Scalar.of_int (1 lsl 32)) big -> false
      | b when equal (shift_right_logical b 26) (Scalar.of_int 0b000101) -> true
      | bcond when equal (shift_right_logical bcond 24) (Scalar.of_int 0b01010100) -> true
      | _ -> false

    (* TODO: unwind the layers of modules to avoid this regrettable hack: *)
    let coerce_pte_val : A.I.V.Cst.PteVal.t -> AArch64PteVal.t = Obj.magic

    type my_v = Label of string
              | Concrete of Scalar.t
              | PTE_Desc_Invalid
              | PTE_Desc of AArch64PteVal.t
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
          raise (Unsupported (sprintf "(db, dbm, el0) = (%d, %d, %d); only (1, 0, 1) is supported" p.db p.dbm p.el0))
        else if 0 = p.AArch64PteVal.valid then
          PTE_Desc_Invalid
        else
          PTE_Desc p
      | Val (Constant.Symbolic (Constant.System (Constant.PTE, sym))) -> PTE_Addr sym
      | v -> Other v

    let pp_v_for_reset v = match v_to_my_v v with
      | Label label -> label ^ ":"
      | Concrete n -> sprintf "extz(%s, 64)" (Scalar.pp true n)
      | PTE_Desc_Invalid -> "extz(0x0, 64)"
      | PTE_Desc p ->
        let open AArch64PteVal in
        begin match (p.oa, p.af) with
          | (OutputAddress.PTE _, _) -> raise (Unsupported "PTE no physical address (intermediate?)")
          | (OutputAddress.PHY phys, 0) -> sprintf "bvxor(extz(0x400, 64), mkdesc3(oa=pa_%s))" phys
          | (OutputAddress.PHY phys, 1) -> sprintf "mkdesc3(oa=pa_%s)" phys
          | (OutputAddress.PHY _, n) -> raise (Unexpected (sprintf "AF (%d) has more than one bit" n))
        end
      | PTE_Addr vaddr -> sprintf "pte3(%s, page_table_base)" vaddr
      | Other v -> A.I.V.pp_v v

    let pp_v_for_assertion = function
      | A.I.V.Val (Constant.Concrete n) -> Scalar.pp (looks_like_branch n) n
      | v -> raise (Unexpected ("Weird value in assertion LV atom: " ^ A.I.V.pp_v v))

    let phys_and_pp_desc_for_page_table_setup p = let open AArch64PteVal in match (p.oa, p.af) with
      | (OutputAddress.PTE _, _) -> raise (Unsupported "PTE no physical address (intermediate?)")
      | (OutputAddress.PHY phys, 0) -> (phys, sprintf "pa_%s with [AF = 0b0]" phys)
      | (OutputAddress.PHY phys, 1) -> (phys, "pa_" ^ phys)
      | (OutputAddress.PHY _, n) -> raise (Unexpected (sprintf "AF (%d) has more than one bit" n))

    let type_name_to_isla_type = function
      | "int8_t" | "uint8_t" -> Some "uint8_t"
      | "int16_t" | "uint16_t" -> Some "uint16_t"
      | "int32_t" | "uint32_t" -> Some "uint32_t"
      | "int64_t" | "uint64_t" -> Some "uint64_t"
      | _ -> None

    let type_to_isla_type t = let open TestType in match t with
      | Ty type_name -> type_name_to_isla_type type_name
      | _ -> None

    let cons_to_list_opt x = function
      | None -> Some [x]
      | Some xs -> Some (x::xs)

    type processed_init =
    {
      branches : ScalarSet.t;
      labels : Label.Set.t;
      addresses : StringSet.t;
      locs : string list;
      inits : (A.reg * string) list IntMap.t;
      types : string StringMap.t;
      pte_set : StringSet.t;
      ptes_accessed : StringSet.t;
      descs_written : StringSet.t;
    }

    let process_init_state test =
      let process_v out = let open A.I.V in function
        | Var i -> raise (Unexpected (sprintf "Encountered Var: %s\n" (pp_csym i))) (* not sure what this is, doesn't trigger anywhere in the tests from HAND *)
        | Val (Constant.Symbolic (Constant.Virtual _ as s)) ->
          { out with addresses = StringSet.add (Constant.pp_symbol s) out.addresses }
        | Val (Constant.Label (_, label)) ->
          { out with labels = Label.Set.add label out.labels }
        | Val (Constant.Concrete instr) when looks_like_branch instr ->
          { out with branches = ScalarSet.add instr out.branches }
        | _ -> out in
      let accum loc v out = let out = process_v out v in match loc with
        | A.Location_reg (proc, reg) ->
           let initialiser = (reg, (quote (pp_v_for_reset v))) in
           let out = match v_to_my_v v with
             | PTE_Desc_Invalid ->
               { out with descs_written = StringSet.add "invalid" out.descs_written }
             | PTE_Desc p ->
               let (phys, desc) = phys_and_pp_desc_for_page_table_setup p in
               { out with descs_written = StringSet.add desc out.descs_written; addresses = StringSet.add phys out.addresses }
             | PTE_Addr vaddr ->
               { out with ptes_accessed = StringSet.add vaddr out.ptes_accessed; addresses = StringSet.add vaddr out.addresses }
             | _ -> out in
           { out with inits = IntMap.update proc (cons_to_list_opt initialiser) out.inits }
        | A.Location_global (A.I.V.Val (Constant.Symbolic (Constant.Virtual _)) as v2) ->
           let out = process_v out v2 in
           let location_name = A.I.V.pp_v v2 in
           let types = let open TestType in match type_to_isla_type (A.look_type test.type_env loc) with
             | Some t -> StringMap.add location_name t out.types
             | None -> out.types in
           let value_str = A.I.V.pp_v v in
           { out with locs = (key_value_str ("*" ^ location_name) value_str)::out.locs; types }
        | A.Location_global (A.I.V.Val (Constant.Symbolic (Constant.System (Constant.PTE, vaddr)))) ->
           begin match v_to_my_v v with
             | PTE_Desc_Invalid -> { out with pte_set = StringSet.add vaddr out.pte_set; locs = (sprintf "%s |-> invalid" vaddr)::out.locs }
             | PTE_Desc p -> { out with pte_set = StringSet.add vaddr out.pte_set; locs = (sprintf "%s |-> %s" vaddr (phys_and_pp_desc_for_page_table_setup p |> snd))::out.locs }
             | _ -> out
           end
        | _ -> out in
      let empty =
        {
          branches = ScalarSet.empty;
          labels = Label.Set.empty;
          addresses = StringSet.empty;
          locs = [];
          inits = IntMap.empty;
          types = StringMap.empty;
          pte_set = StringSet.empty;
          ptes_accessed = StringSet.empty;
          descs_written = StringSet.empty;
        } in
      A.state_fold accum test.init_state empty

    let to_sail_general_reg reg =
      let xreg = A.pp_reg reg in
      if xreg.[0] <> 'X' then
        failwith "to_sail_general_reg: not general-purpose register"
      else
        "R" ^ String.sub xreg 1 (String.length xreg - 1)

    let print_threads test inits addr_to_labels threads_with_faults info =
      let print_thread (proc, code, x) =
        let has_faults = Option.is_some (IntSet.find_opt proc threads_with_faults) in
        print_newline ();
        Option.iter (fun _ -> raise (Unexpected "Encountered a Some")) x; (* what is this? *)
        printf "[thread.%s]\n" (Proc.dump proc);
        (* print_key "init" (sprintf "{ %s }" (IntMap.find_opt proc inits |> Option.value ~default:[] |> String.concat ", ")); *)
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
        let end_label = sprintf "islaconv_%s_end" (A.pp_proc proc) in
        if has_faults && info.precision = Precision.Fatal then print_endline (end_label ^ ":");
        print_endline "\"\"\"";
        print_newline ();
        printf "[thread.%s.reset]\n" (Proc.dump proc);
        List.iter (fun (r, v) -> print_key (to_sail_general_reg r) v) (IntMap.find_opt proc inits |> Option.value ~default:[]);
        if Option.is_none (IntSet.find_opt proc info.el0_threads) then
          print_key "\"PSTATE.EL\"" "0x01"; (* herd EL1 by default *)
        if has_faults then begin
          print_key "VBAR_EL1" (sprintf "\"extz(%#x000, 64)\"" (1 + proc));
          print_key "R12" "\"extz(0x0, 64)\"";
          print_newline ();
          printf "[section.thread%s_el1_handler]\n" (Proc.dump proc);
          print_key "address" (sprintf "\"%#x400\"" (1 + proc));
          print_endline "code = \"\"\"";
          print_endline "\tMRS X12,ELR_EL1";
          begin match info.precision with
            | Precision.Handled -> ()
            | Precision.Fatal ->
              print_endline ("\tMOV X14," ^ end_label);
              print_endline "\tMSR ELR_EL1,X14"
            | Precision.LoadsFatal -> raise (Unsupported "LoadsFatal precision setting")
            (* LoadsFatal is undocumented and doesn't appear in the tests in catalogue *)
            | Precision.Skip ->
              print_endline "\tMRS X14,ELR_EL1";
              print_endline "\tADD X14,X14,#4";
              print_endline "\tMSR ELR_EL1,X14" end;
          print_endline "\tERET";
          print_endline "\"\"\""
        end in
      List.iter print_thread test.start_points

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

    let rec fold_expr f a = let open ConstrGen in function
      | Atom atom -> f a atom
      | Not expr -> fold_expr f a expr
      | And exprs | Or exprs -> List.fold_left (fold_expr f) a exprs
      | Implies (l, r) -> fold_expr f (fold_expr f a l) r

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

    (*let print_section_as_lines section lines =
      if lines <> [] then begin
        print_newline ();
        printf "[%s]\n" section;
        List.iter print_endline lines
      end*)

    let print_types types =
      if not (StringMap.is_empty types) then begin
        print_newline ();
        print_endline "[types]";
        StringMap.iter (fun k v -> print_endline (key_value_str (quote k) (quote v))) types
      end

    let print_page_table_setup nthreads threads_with_faults addresses locs pte_unset ptes_accessed descs_written =
      print_newline ();
      print_endline "page_table_setup = \"\"\"";
      printf "\tphysical %s;\n" (String.concat " " (List.map ((^) "pa_") addresses));
      StringSet.iter (fun addr -> printf "\t%s |-> pa_%s;\n" addr addr) pte_unset;
      List.iter (printf "\t%s;\n") locs;
      StringSet.iter (fun sym -> StringSet.iter (printf "\t%s ?-> %s;\n" sym) descs_written) ptes_accessed;
      for proc = 0 to nthreads - 1 do
        if Option.is_some (IntSet.find_opt proc threads_with_faults) then
          printf "\tidentity %#x000 with code;\n" (1 + proc)
      done;
      print_endline "\"\"\""

    let find_threads_with_faults test =
      let check_atom threads = function
        | ConstrGen.FF ((proc, _), _, _) -> IntSet.add proc threads
        | _ -> threads in
      fold_expr check_atom IntSet.empty (snd (expect_and_expr (test.cond)))

(* TODO: checking PTEs in assertions? *)
(* not relevant/don't know how to do: setting db/dbm *)

    let print_converted (test : T.result) =
      let { branches; labels; addresses; locs; inits; types; pte_set; ptes_accessed; descs_written } = process_init_state test in
      let info = print_header_and_parse_info test addresses in
      Label.Set.iter (print_selfmodify test branches) labels;
      let threads_with_faults = find_threads_with_faults test in
      print_page_table_setup (List.length test.start_points) threads_with_faults (StringSet.elements addresses) locs (StringSet.diff addresses pte_set) ptes_accessed descs_written;
      print_types (StringSet.fold (fun vaddr types -> StringMap.update vaddr (function | Some t -> Some t | None -> Some "uint64_t") types) addresses types);
      print_threads test inits (addr_to_labels test) threads_with_faults info;
      print_final test
  end
