(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2023-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

module type Config = sig
  val model : Model.t option
  val archcheck : bool
  val through : Model.through
  val strictskip : bool
  val cycles : StringSet.t
  val bell_model_info : (string * BellModel.info) option
  val macros : string option
  val check_name : string -> bool
  val check_rename : string -> string option
  val libfind : string -> string
  include GenParser.Config
  include Top_herd.CommonConfig
  include Sem.Config

  val statelessrc11 : bool
  val dumpallfaults : bool
  val byte : MachSize.Tag.t
  val sve_vector_length : int
  val sme_vector_length : int
end

type runfun =
  DirtyBit.t option ->
  float (* start time *) ->
  string (* file name *) ->
  in_channel (* source channel *) ->
  TestHash.env ->
  Splitter.result ->
  TestHash.env

module Make
    (S:Sem.Semantics)
    (P:sig
      type pseudo
      val parse : in_channel -> Splitter.result ->  pseudo MiscParser.t
    end with type pseudo = S.A.pseudo)
    (M:XXXMem.S with module S = S)
    (C:Config) =
  struct
    module T = Test_herd.Make(S.A)
     let run dirty start_time filename chan env splitted =
      try
         let parsed = P.parse chan splitted in
        let name = splitted.Splitter.name in
        let hash = MiscParser.get_hash parsed in
        let env = match hash with
        | None -> env
        | Some hash ->
            TestHash.check_env env name.Name.name filename hash in
        let test = T.build name parsed in
(* Compute basic machine size *)
        let sz =
          if S.A.is_mixed then begin match C.byte with
          | MachSize.Tag.Size sz -> sz
          | MachSize.Tag.Auto ->
              let szs = test.Test_herd.access_size in
              match szs with
              | [] -> MachSize.Byte
              | [sz] -> MachSize.pred sz
              | sz::_ -> sz (* Do not split the smallest size involved *)
          end else begin
            (* Cannot that easily check the test not to mix sizes,
               as there are several locations in test that may be of
               different sizes *)
            MachSize.Byte
          end in
        Printf.printf "arch = \"%s\"\nname = \"%s\"\n" (Archs.pp S.A.arch) test.name.Name.name;
        (* Note: replace below warning with escaping (check that this is sane by looking up TOML format) *)
        List.iter (fun (k, v) -> (if String.contains v '"' then print_endline "Warning: value contains quotes; output might be garbled"); Printf.printf "%s = \"%s\"\n" (String.lowercase_ascii k) v) test.info;
        print_endline "addresses = TODO\n\n[locations]";
        let inits = ref IntMap.empty in
        List.iter (fun (loc, v) -> match loc with | S.A.Location_reg (proc, reg) -> inits := IntMap.update proc (let app = Printf.sprintf "%s = \"%s\"" (S.A.pp_reg reg) (S.A.I.V.pp_v v) in function | None -> Some [app] | Some xs -> Some (app :: xs)) !inits | S.A.Location_global v2 -> Printf.printf "\"%s\" = \"%s\"\n" (S.A.I.V.pp_v v2) (S.A.I.V.pp_v v)) (S.A.state_to_list test.init_state);
        print_newline ();
        (* IntMap.iter (fun i (proc, code) -> Printf.printf "[thread.%s] note: %d\ninit = TODO\ncode = \"\"\"\n" (Proc.dump proc) i; List.iter (fun (_, instr) -> Printf.printf "    %s\n" (S.A.dump_instruction instr)) code; print_endline "\"\"\"") test.code_segment; *)
        List.iter (fun (proc, code, _) -> Printf.printf "[thread.%s]\ninit = { %s }\ncode = \"\"\"\n" (Proc.dump proc) (String.concat ", " (IntMap.find proc !inits)); List.iter (fun (_, instr) -> Printf.printf "\t%s\n" (S.A.dump_instruction instr)) code; print_endline "\"\"\"\n") test.start_points; (* TODO restore labels *)
        print_endline "[final]\nTODO";
        (* print_endline (S.A.pp_state test.init_state);
        List.iter (fun (loc, v) -> match loc with | S.A.Location_reg (proc, reg) -> (Printf.printf "%s:%s=%s\n" (Proc.dump proc) (S.A.pp_reg reg) (S.A.I.V.pp_v v)) | S.A.Location_global v2 -> Printf.printf "%s %s\n" (S.A.I.V.pp_v v2) (S.A.I.V.pp_v v)) (S.A.state_to_list test.init_state); *)
(* And run test *) (* actually, don't *)
        (* let module T =
          Top_herd.Make
            (struct
              include C
              let byte = sz
              let dirty = dirty
            end)(M) in
        T.run start_time test ; *)
        env
      with TestHash.Seen -> env
  end
