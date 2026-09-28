import PoincareConjecture.Proofs.M76.Rigidity.OriginalRegularClosedCut
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeRegionClosure

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

namespace OriginalDiskProduct

theorem closure_openStrip (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    closure P.openStrip = P.closedStrip := by
  have hUC : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hC : IsClosed P.closedStrip :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  have hIC : interior P.closedStrip ⊆ P.openStrip := by
    change interior (P.map '' (closedBall (0 : V2) 1 ×ˢ
      Icc (-(1 / 2 : ℝ)) (1 / 2))) ⊆ _
    rw [P.interior_closed_strip (by norm_num : (1 / 2 : ℝ) < 1) hopen]
    exact image_mono (prod_mono ball_subset_closedBall subset_rfl)
  have hreg : closure (interior P.closedStrip) = P.closedStrip :=
    P.closure_interior_closed_strip (by norm_num) (by norm_num) hopen
  apply Subset.antisymm (closure_minimal hUC hC)
  rw [← hreg]
  exact closure_mono hIC

theorem relative_frontier_cut (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    frontier ((Subtype.val : R → X) ⁻¹' P.cutCarrier) =
      (Subtype.val : R → X) ⁻¹' P.endDisks := by
  have hUR : P.openStrip ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact P.inside ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  change frontier ((Subtype.val : R → X) ⁻¹' (R \ P.openStrip)) = _
  rw [frontier_subtype_cut_of_closure hUR hopen (P.closure_openStrip hopen),
    P.closedStrip_sdiff_openStrip]

theorem relative_regular_closed_cut (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    closure (interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier)) =
      (Subtype.val : R → X) ⁻¹' P.cutCarrier :=
  regular_closed_subtype_preimage (P.cut_geometry hR hopen).1.isClosed
    sdiff_subset (P.closure_interior_cut hR he hopen)

end OriginalDiskProduct
end PoincareConjecture.M76
