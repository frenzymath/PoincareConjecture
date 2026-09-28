import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedCoefficients
import PoincareConjecture.Proofs.M01.NormalizationScaling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.SurgeryCapClose

local notation "E" => StandardCapSpace

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}

theorem normalizedCoefficients_symm (Q : SurgeryCapClose g₀ S g tip scale eta)
    (x v w : E) : Q.normalizedCoefficients x v w = Q.normalizedCoefficients x w v := by
  simp only [normalizedCoefficients_apply, g.symm]

theorem normalizedCoefficients_pos (Q : SurgeryCapClose g₀ S g tip scale eta)
    {x : E} (hx : x ∈ g₀.metric.ball 0 eta⁻¹) {v : E} (hv : v ≠ 0) :
    0 < Q.normalizedCoefficients x v v := by
  have hD := Poincare.mfderiv_bijective_of_smooth_leftInvOn
    Q.toPartialDiffeomorph.open_source Q.map_smooth Q.inverse_smooth Q.left_inverse hx
  have hDv : mfderiv (𝓡 3) (𝓡 3) Q.map x v ≠ 0 := by
    intro hzero
    exact hv (hD.1 (by simpa only [map_zero] using hzero))
  rw [Q.normalizedCoefficients_apply]
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr Q.scale_pos)) (g.pos _ _ hDv)

theorem normalizedCoefficients_isInvertible (Q : SurgeryCapClose g₀ S g tip scale eta)
    {x : E} (hx : x ∈ g₀.metric.ball 0 eta⁻¹) :
    (Q.normalizedCoefficients x).IsInvertible := by
  let h := m01RescaledMetric g (scale⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr Q.scale_pos))
  have hD := Poincare.mfderiv_bijective_of_smooth_leftInvOn
    Q.toPartialDiffeomorph.open_source Q.map_smooth Q.inverse_smooth Q.left_inverse hx
  have heq : Q.normalizedCoefficients x = h.pullbackCoefficients Q.map x := by
    ext v w
    rfl
  rw [heq]
  exact h.isInvertible_pullbackCoefficients hD.1

theorem exists_normalized_uniform_lower_bound
    (g₀ : StandardInitialMetric) {K : Set E} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : GeneralizedSliceCarrier.{u})
      (g : RiemannianMetric 3 S.carrier) (tip : S.carrier) (scale eta : ℝ)
      (Q : SurgeryCapClose g₀ S g tip scale eta),
      eta ≤ 1 / 2 → K ⊆ g₀.metric.ball 0 eta⁻¹ → ∀ x ∈ K, ∀ v : E,
        c * ‖v‖ ^ 2 ≤ Q.normalizedCoefficients x v v := by
  have hg : Continuous g₀.metric.euclideanCoefficients :=
    (contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients).continuous
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound hK hg.continuousOn
    (fun x _ v hv => g₀.metric.pos x v hv)
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro S g tip scale eta Q heta hKU x hx v
  have hgpos : 0 ≤ g₀.metric.inner x v v :=
    (mul_nonneg hc.le (sq_nonneg ‖v‖)).trans (hbound x hx v)
  calc
    c / 2 * ‖v‖ ^ 2 = (1 / 2) * (c * ‖v‖ ^ 2) := by ring
    _ ≤ (1 / 2) * g₀.metric.inner x v v :=
      mul_le_mul_of_nonneg_left (hbound x hx v) (by norm_num)
    _ ≤ (1 - eta) * g₀.metric.inner x v v :=
      mul_le_mul_of_nonneg_right (by linarith) hgpos
    _ ≤ Q.normalizedCoefficients x v v := (Q.quadratic_bounds (hKU hx) v).1

end PoincareConjecture.SurgeryCapClose

namespace PoincareConjecture.M44

theorem exists_standard_geodesicField_lipschitz
    (g₀ : StandardInitialMetric) {K : Set (StandardCapSpace × StandardCapSpace)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∃ L : ℝ≥0, LipschitzOnWith L (coordinateGeodesicField g₀.metric.euclideanCoefficients) K := by
  let V := coordinateGeodesicField g₀.metric.euclideanCoefficients
  have hV : ContDiff ℝ ∞ V := contDiff_iff_contDiffAt.mpr fun z =>
    contDiffAt_coordinateGeodesicField (g₀.metric.contDiffAt_euclideanCoefficients z.1)
      (g₀.metric.inner_isInvertible z.1)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hV.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun z _ => hV.differentiable (by simp) z) ?_ hconv
  intro z hz
  exact (hC z hz).trans (le_max_left _ _)

end PoincareConjecture.M44
