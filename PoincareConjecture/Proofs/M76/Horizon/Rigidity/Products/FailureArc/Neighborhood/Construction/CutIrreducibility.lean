import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.OriginalCompressionNeighborhood

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalDiskProduct.isOpen_openStrip_of_isCompact_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hcut : IsCompact P.cutCarrier) :
    IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) := by
  have heq : ((Subtype.val : R → X) ⁻¹' P.openStrip) =
      ((Subtype.val : R → X) ⁻¹' P.cutCarrier)ᶜ := by
    ext x
    simp [OriginalDiskProduct.cutCarrier, x.property]
  rw [heq]
  exact (hcut.isClosed.preimage continuous_subtype_val).isOpen_compl

theorem OriginalDiskProduct.isPLIrreducible_cut_of_isCompact
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (hcut : IsCompact P.cutCarrier)
    (hI : IsPLIrreducible e R) : IsPLIrreducible e P.cutCarrier :=
  P.isPLIrreducible_cut hR hI (P.isOpen_openStrip_of_isCompact_cut hcut)

end PoincareConjecture.M76
