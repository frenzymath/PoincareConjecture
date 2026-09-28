import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.AffineComposition
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def koszulCovectorMap (u v : E) :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (show (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ) from
    { toFun := fun A => metricKoszulCovector A u v
      map_add' := by intros; ext w; simp [metricKoszulCovector]; ring
      map_smul' := by intros; ext w; simp [metricKoszulCovector]; ring }).toContinuousLinearMap

theorem norm_koszulCovectorMap_le (u v : E) :
    ‖koszulCovectorMap u v‖ ≤ (3 / 2 : ℝ) * ‖u‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  change ‖metricKoszulCovector A u v‖ ≤ _
  exact (norm_metricKoszulCovector_le A u v).trans_eq (by ring)

theorem norm_iteratedFDeriv_koszulCovector_le
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : ContDiffAt ℝ ∞ B x) (q : ℕ) (u v : E) :
    ‖iteratedFDeriv ℝ q (fun y => metricKoszulCovector (fderiv ℝ B y) u v) x‖ ≤
      (3 / 2 : ℝ) * ‖iteratedFDeriv ℝ (q + 1) B x‖ * ‖u‖ * ‖v‖ := by
  have h := (koszulCovectorMap u v).norm_iteratedFDeriv_comp_left
    (hB.fderiv_right (by simp)) (show (q : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ q (fun y => metricKoszulCovector (fderiv ℝ B y) u v) x‖ ≤ _ at h
  rw [norm_iteratedFDeriv_fderiv] at h
  calc
    _ ≤ ‖koszulCovectorMap u v‖ * ‖iteratedFDeriv ℝ (q + 1) B x‖ := h
    _ ≤ ((3 / 2 : ℝ) * ‖u‖ * ‖v‖) * ‖iteratedFDeriv ℝ (q + 1) B x‖ :=
      mul_le_mul_of_nonneg_right (norm_koszulCovectorMap_le u v) (norm_nonneg _)
    _ = _ := by ring

theorem norm_iteratedFDeriv_christoffel_apply_le
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : ContDiffAt ℝ ∞ B x) (hi : (B x).IsInvertible) (q : ℕ) (u v : E) :
    ‖iteratedFDeriv ℝ q (fun y => christoffelBilinear B y u v) x‖ ≤
      (3 / 2 : ℝ) * (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖ *
        ‖iteratedFDeriv ℝ (q - i + 1) B x‖) * ‖u‖ * ‖v‖ := by
  have hInv := hi.contDiffAt_map_inverse.comp x hB
  have hKoszul : ContDiffAt ℝ ∞
      (fun y => metricKoszulCovector (fderiv ℝ B y) u v) x :=
    (koszulCovectorMap u v).contDiff.contDiffAt.comp x (hB.fderiv_right (by simp))
  have h := norm_iteratedFDeriv_bilinear_le_of_contDiffAt
    (ContinuousLinearMap.id ℝ ((E →L[ℝ] ℝ) →L[ℝ] E)) hInv hKoszul q
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖ *
      ‖iteratedFDeriv ℝ (q - i) (fun y => metricKoszulCovector (fderiv ℝ B y) u v) x‖ :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h' := h.trans (mul_le_of_le_one_left hsum0 (ContinuousLinearMap.norm_id_le))
  change ‖iteratedFDeriv ℝ q (fun y => christoffelBilinear B y u v) x‖ ≤ _ at h'
  apply h'.trans
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖ *
        ((3 / 2 : ℝ) * ‖iteratedFDeriv ℝ (q - i + 1) B x‖ * ‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_koszulCovector_le hB (q - i) u v)
        (by positivity)
    _ = _ := by ring

end PoincareConjecture.SpacetimeBounds
