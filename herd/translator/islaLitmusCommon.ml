module Make (A:Arch_herd.S) = struct
  include IslaLitmusErrors

  let sprintf = Printf.sprintf

  let key_value_str = sprintf "%s = %s"

  let get_physical_address p = match p.AArch64PteVal.oa with
    | OutputAddress.PTE _ -> raise (Unsupported "Output address is PTE (intermediate entry?)")
    | OutputAddress.PHY phys -> phys
  
  let pp_v_for_reset cst =
    let module Test = IslaLitmusTest.Make(A) in
    let module Desc = Test.Desc in
    match Desc.of_cst cst with
      | Some (Desc.Valid p) ->
        let open AArch64PteVal in
        begin match (p.oa, p.af) with
          | (OutputAddress.PTE _, _) -> raise (Unsupported "PTE no physical address (intermediate?)")
          | (OutputAddress.PHY phys, 0) -> sprintf "bvxor(extz(0x400, 64), mkdesc3(oa=pa_%s))" phys (* TODO *)
          | (OutputAddress.PHY phys, 1) -> sprintf "mkdesc3(oa=pa_%s)" phys
          | (OutputAddress.PHY _, n) -> raise (Unexpected (sprintf "AF (%d) has more than one bit" n))
        end
      | Some Desc.Invalid -> "extz(0x0, 64)"
      | None -> let open Constant in match cst with
        | Label (_, label) -> label ^ ":"
        | Concrete n -> sprintf "extz(%s, 64)" (A.V.Cst.Scalar.pp true n)
        | Symbolic (System (PTE, addr)) -> sprintf "pte3(%s, page_table_base)" addr
        | v -> A.V.Cst.pp_v v
end