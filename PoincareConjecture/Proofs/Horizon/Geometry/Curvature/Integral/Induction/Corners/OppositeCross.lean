import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Tightening







noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace Poincare.CurvatureIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem norm_add_le_of_opposite
    (u v : E) {η : ℝ} (hη : 0 ≤ η) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hpair : ⟪u, v⟫_ℝ ≤ -1 + 2 * η) :
    ‖u + v‖ ≤ 2 * Real.sqrt η := by
  have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hadd := norm_add_sq_real u v
  have hsqrt := Real.sq_sqrt hη
  have hnonneg := Real.sqrt_nonneg η
  nlinarith [norm_nonneg (u + v)]


theorem abs_inner_opposite_le
    (u v w : E) {ε η : ℝ} (hη : 0 ≤ η)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hpair : ⟪u, v⟫_ℝ ≤ -1 + 2 * η)
    (hcross : |⟪u, w⟫_ℝ| ≤ ε) :
    |⟪v, w⟫_ℝ| ≤ ε + 2 * Real.sqrt η := by
  apply abs_inner_le_of_strainer_perturbation (-u) v w hw
  · simpa only [sub_neg_eq_add, add_comm] using norm_add_le_of_opposite u v hη hu hv hpair
  · simpa only [inner_neg_left, abs_neg] using hcross


theorem abs_inner_opposite_le_of_square_error
    (u v w : E) {ε : ℝ} (hε : 0 ≤ ε)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hpair : ⟪u, v⟫_ℝ ≤ -1 + ε ^ 2 / 8)
    (hcross : |⟪u, w⟫_ℝ| ≤ ε / 2) :
    |⟪v, w⟫_ℝ| ≤ ε := by
  have hsum : ‖u + v‖ ≤ ε / 2 := by
    have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    have hadd := norm_add_sq_real u v
    nlinarith [norm_nonneg (u + v)]
  have h := abs_inner_le_of_strainer_perturbation (-u) v w hw
    (by simpa only [sub_neg_eq_add, add_comm] using hsum)
    (by simpa only [inner_neg_left, abs_neg] using hcross)
  linarith


theorem abs_inner_opposite_le_of_annular_error
    (u v w : E) {ε η : ℝ} (hε : 0 ≤ ε)
    (hη : η ≤ ε ^ 2 / 1024)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hpair : ⟪u, v⟫_ℝ ≤ -1 + 128 * η)
    (hcross : |⟪u, w⟫_ℝ| ≤ ε / 2) :
    |⟪v, w⟫_ℝ| ≤ ε := by
  apply abs_inner_opposite_le_of_square_error u v w hε hu hv hw _ hcross
  linarith
theorem opposite_cross_bounds_of_small_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (f h : Fin k → E) {δ ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ (ε / 256) ^ 2)
    (hpair : ∀ i, ‖f i‖ ≤ 1 ∧ ‖h i‖ ≤ 1 ∧ ⟪f i, h i⟫_ℝ ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j → |⟪f i, f j⟫_ℝ| ≤ δ ∧ |⟪h i, f j⟫_ℝ| ≤ δ) :
    ∀ i j, i ≠ j → |⟪f i, f j⟫_ℝ| ≤ ε ∧
      |⟪h i, f j⟫_ℝ| ≤ ε ∧ |⟪h i, h j⟫_ℝ| ≤ ε := by
  have hroot : Real.sqrt δ ≤ ε / 256 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hδsmall⟩
  have hδle : δ ≤ ε := by nlinarith
  have hbudget : δ + 2 * Real.sqrt δ ≤ ε := by nlinarith
  intro i j hij
  refine ⟨(hcross i j hij).1.trans hδle, (hcross i j hij).2.trans hδle, ?_⟩
  have hh := abs_inner_opposite_le (f j) (h j) (h i) hδ
    (hpair j).1 (hpair j).2.1 (hpair i).2.1 (hpair j).2.2
    (by simpa only [real_inner_comm] using (hcross i j hij).2)
  simpa only [real_inner_comm] using hh.trans hbudget

end Poincare.CurvatureIntegral
