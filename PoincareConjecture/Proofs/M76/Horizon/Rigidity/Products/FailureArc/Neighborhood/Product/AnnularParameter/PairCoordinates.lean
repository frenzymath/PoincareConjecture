import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinalBallAnnulusTransport

set_option autoImplicit false
noncomputable section
open Set Metric

namespace PoincareConjecture.M76.Dehn.Annuli.AnnularParameter

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)

def pairCoordinates : V2 ≃L[ℝ] P2 := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

theorem pairCoordinates_norm (z : V2) : ‖pairCoordinates z‖ = ‖z‖ := by
  change max ‖z 0‖ ‖z 1‖ = ‖z‖
  apply le_antisymm
  · exact max_le (norm_le_pi_norm z 0) (norm_le_pi_norm z 1)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem pairCoordinates_rim (z : V2) :
    z ∈ sphere (0 : V2) 1 ↔ pairCoordinates z ∈ sphere (0 : P2) 1 := by
  simp only [mem_sphere, dist_zero_right, pairCoordinates_norm]

theorem pairCoordinates_rim_surjective (z : sphere (0 : P2) 1) :
    ∃ v : sphere (0 : V2) 1, pairCoordinates v = z := by
  refine ⟨⟨pairCoordinates.symm z, ?_⟩, pairCoordinates.apply_symm_apply z⟩
  apply (pairCoordinates_rim _).mpr
  simpa only [pairCoordinates.apply_symm_apply] using z.property

end PoincareConjecture.M76.Dehn.Annuli.AnnularParameter
