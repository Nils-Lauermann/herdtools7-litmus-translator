module Make (A:Arch_herd.S) = struct
  include IslaLitmusErrors

  let sprintf = Printf.sprintf

  let key_value_str = sprintf "%s = %s"

  let get_physical_address p = match p.AArch64PteVal.oa with
    | OutputAddress.PTE _ -> raise (Unsupported "Output address is PTE (intermediate entry?)")
    | OutputAddress.PHY phys -> phys
  
  let pp_v_for_reset cst =
    let open AArch64PteVal in
    let flip_for p = (* Note: assuming the defaults are the same as for isla *)
      let mask = 0 in
      let mask = if p.af <> 1 then mask lor (1 lsl 10) else mask in
      let mask = if p.db <> 1 then mask lor (1 lsl 7) else mask in
      let mask = if p.el0 <> 1 then mask lor (1 lsl 6) else mask in
      if mask = 0 then None else Some mask in
    let module Test = IslaLitmusTest.Make(A) in
    let module Desc = Test.Desc in
    match Desc.of_cst cst with
      | Some (Desc.Valid p) ->
        let mask = flip_for p in
        begin match (p.oa, mask) with
          | (OutputAddress.PTE _, _) -> raise (Unsupported "PTE no physical address (intermediate?)")
          | (OutputAddress.PHY phys, Some mask) -> sprintf "bvxor(extz(%#x, 64), mkdesc3(oa=pa_%s))" mask phys
          | (OutputAddress.PHY phys, None) -> sprintf "mkdesc3(oa=pa_%s)" phys
        end
      | Some Desc.Invalid -> "extz(0x0, 64)"
      | None -> let open Constant in match cst with
        | Label (_, label) -> label ^ ":"
        | Concrete n -> sprintf "extz(%s, 64)" (A.V.Cst.Scalar.pp true n)
        | Symbolic (System (PTE, addr)) -> sprintf "pte3(%s, page_table_base)" addr
        | v -> A.V.Cst.pp_v v
end