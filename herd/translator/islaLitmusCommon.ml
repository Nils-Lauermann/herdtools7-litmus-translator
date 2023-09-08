include IslaLitmusErrors

let key_value_str = Printf.sprintf "%s = %s"

let get_physical_address p = match p.AArch64PteVal.oa with
  | OutputAddress.PTE _ -> raise (Unsupported "Output address is PTE (intermediate entry?)")
  | OutputAddress.PHY phys -> phys