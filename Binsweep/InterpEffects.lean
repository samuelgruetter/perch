import Kraken.X64.Semantics

def Effects.Exists (es : Effects) (final : MachineState) : Prop :=
  match es with
  | .done result => result = final
  | .unimplemented .. => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∃ v : α, (cont v).Exists final
  | .require_read_access _ _ ok => (ok ()).Exists final
  | .require_write_access _ _ ok => (ok ()).Exists final
  | .require_exec_access _ ok => (ok ()).Exists final
