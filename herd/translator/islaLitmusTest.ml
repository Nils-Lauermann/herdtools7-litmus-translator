open IslaLitmusErrors

module Make (A:Arch_herd.S) = struct
  module Scalar = A.V.Cst.Scalar
  module ScalarSet = Set.Make(Scalar)
  module ProcMap = Map.Make(Proc)
  module ProcSet = Set.Make(Proc)
  module RegSet = Set.Make(struct type t = A.reg let compare = A.reg_compare end)

  let v_to_cst = function
    | A.V.Var i -> raise (Unexpected (Printf.sprintf "Encountered Var: %s\n" (A.V.pp_csym i))) (* Not sure what this is, doesn't trigger anywhere in the tests I've tried *)
    | A.V.Val cst -> cst

  module Info = struct
    type t =
      {
        handling : Fault.Handling.t;
        el0_threads : ProcSet.t;
        other_info : (string * string) list;
      }

    let empty =
      {
        handling = Fault.Handling.Fatal;
        el0_threads = ProcSet.empty;
        other_info = [];
      }
  end

  module Desc = struct
    type t =
      | Invalid
      | Valid of AArch64PteVal.t

    let equal lhs rhs = match (lhs, rhs) with
      | (Invalid, Invalid) -> true
      | (Valid lhs, Valid rhs) -> AArch64PteVal.eq lhs rhs
      | _ -> false

    let compare lhs rhs = match (lhs, rhs) with
      | (Invalid, Invalid) -> 0
      | (Invalid, Valid _) -> -1
      | (Valid _, Invalid) -> 1
      | (Valid lhs, Valid rhs) -> AArch64PteVal.compare lhs rhs

    let of_cst = function
      | Constant.PteVal p ->
        (* TODO: unwind the layers of modules to avoid this regrettable hack: *)
        let coerce_pte_val : A.I.V.Cst.PteVal.t -> AArch64PteVal.t = Obj.magic in
        let p = coerce_pte_val p in
        let open AArch64PteVal in
        if p.dbm <> 0 then
          raise (Unsupported (Printf.sprintf "dbm = %d; only 0 is supported" p.dbm))
        else if p.AArch64PteVal.valid = 0 then
          Some Invalid
        else
          Some (Valid p)
      | _ -> None
  end

  module DescSet = Set.Make(Desc)

  module PageTableSetup = struct
    type t =
    {
      physical_addresses : StringSet.t;
      initial_mappings : Desc.t StringMap.t;
      possible_mappings : DescSet.t StringMap.t;
      initial_values : Scalar.t StringMap.t;
    }

    let empty =
    {
      physical_addresses = StringSet.empty;
      initial_mappings = StringMap.empty;
      possible_mappings = StringMap.empty;
      initial_values = StringMap.empty;
    }
  end

  (* Fault information for tracking in exception handlers *)
  type fault_info = {
    label: string option;
    location: A.V.Cst.v option;  (* symbolic location value for initialization *)
    fault_type: string option;
    predicate_reg: A.reg option;  (* initialized to location address if present, then set to 1 if all conditions satisfied *)
  }

  module Thread = struct
    type t =
    {
      instructions : (int * A.instruction) list;
      reset : (A.reg * A.V.Cst.v) list;
      reset_extra : (string * string) list;
      fault_handler : (int * A.instruction) list option;
      ptes_accessed : StringSet.t;
      descs_written : DescSet.t;
      (* Free registers available for translator infrastructure needs.
         Computed as: all allowed registers minus those used in instructions,
         fault handlers, and initial state. Allocated on-demand during conversion
         for fault predicates. After conversion, remaining free registers are used
         as temporary registers during printing (e.g., for fault handler checks).
         Updated after each allocation to track remaining free registers. *)
      free_registers : A.reg list;
      fault_predicates : fault_info list;
    }

    let empty =
    {
      instructions = [];
      reset = [];
      reset_extra = [];
      fault_handler = None;
      ptes_accessed = StringSet.empty;
      descs_written = DescSet.empty;
      free_registers = [];
      fault_predicates = [];
    }
  end

  module Expect = struct
    type t =
      | Satisfiable
      | Unsatisfiable
  end

  module Final = struct
    type t =
    {
      expect : Expect.t;
      assertion : string;
    }

    let empty = (* this shouldn't really exist *)
    {
      expect = Expect.Satisfiable;
      assertion = "true";
    }
  end

  type t =
  {
    arch : Archs.t;
    name : string;
    info : Info.t;
    label_constants : Label.Set.t;
    branch_constants : ScalarSet.t;
    addresses : StringSet.t;
    locations : (string * A.V.Cst.v) list;
    page_table_setup : PageTableSetup.t;
    types : string StringMap.t;
    threads : Thread.t ProcMap.t;
    labels : int Label.Map.t;
    addr_to_instr : A.instr IntMap.t;
    final : Final.t;
  }

  let empty arch name num_threads =
    let rec empty_threads i threads =
      if i = num_threads then
        threads
      else
        empty_threads (1 + i) (ProcMap.add i Thread.empty threads) in
    {
      arch = arch;
      name = name;
      info = Info.empty;
      label_constants = Label.Set.empty;
      branch_constants = ScalarSet.empty;
      addresses = StringSet.empty;
      locations = [];
      page_table_setup = PageTableSetup.empty;
      types = StringMap.empty;
      threads = empty_threads 0 ProcMap.empty;
      labels = Label.Map.empty;
      addr_to_instr = IntMap.empty;
      final = Final.empty;
    }
end