import PoincareConjecture.Proofs.M76.Rigidity.OriginalStripInterior
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.isCompact_closed_strip (P : OriginalDiskProduct e R j)
    {δ : ℝ} (hδ : δ ≤ 1) :
    IsCompact (P.map '' (D ×ˢ Icc (-δ) δ)) := by
  apply ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc).image_of_continuousOn
  apply P.polyhedral.continuousOn.mono
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem OriginalDiskProduct.closure_interior_closed_strip [T2Space X]
    (P : OriginalDiskProduct e R j) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D ×ˢ Ioo (-δ) δ)))) :
    closure (interior (P.map '' (D ×ˢ Icc (-δ) δ))) =
      P.map '' (D ×ˢ Icc (-δ) δ) := by
  rw [P.interior_closed_strip hδ1 hopen]
  have hclosure : closure (ball (0 : V2) 1 ×ˢ Ioo (-δ) δ) =
      D ×ˢ Icc (-δ) δ := by
    rw [closure_prod_eq, closure_ball _ one_ne_zero, closure_Ioo (by linarith : -δ ≠ δ)]
  apply Subset.antisymm
  · exact closure_minimal
      (image_mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self))
      (P.isCompact_closed_strip hδ1.le).isClosed
  · have hc : ContinuousOn P.map (closure (ball (0 : V2) 1 ×ˢ Ioo (-δ) δ)) := by
      rw [hclosure]
      apply P.polyhedral.continuousOn.mono
      intro z hz
      exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have h := hc.image_closure
    rwa [hclosure] at h

end PoincareConjecture.M76
