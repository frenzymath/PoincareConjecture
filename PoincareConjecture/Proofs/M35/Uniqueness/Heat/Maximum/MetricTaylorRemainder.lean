import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricPotential
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricTestBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem covector_norm_le_basis_sum (A : V →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ j, ‖A (EuclideanSpace.single j (1 : ℝ))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have he := congrArg A ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  simp only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply] at he
  rw [← he, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (EuclideanSpace.basisFun (Fin n) ℝ).repr.norm_map v ▸
    PiLp.norm_apply_le ((EuclideanSpace.basisFun (Fin n) ℝ).repr v) j

theorem quadratic_remainder_of_derivative_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hf : ∀ z, HasFDerivAt f (D z) z)
    {C : ℝ} (hC : 0 ≤ C) (hD : ∀ z w, ‖D z - D w‖ ≤ C * ‖z - w‖) (z w : E) :
    ‖f w - f z - D z (w - z)‖ ≤ C * ‖w - z‖ ^ 2 := by
  have hd (y : E) (_ : y ∈ segment ℝ z w) :
      HasFDerivWithinAt (fun v => f v - D z v) (D y - D z) (segment ℝ z w) y :=
    ((hf y).sub (D z).hasFDerivAt).hasFDerivWithinAt
  have hb (y : E) (hy : y ∈ segment ℝ z w) : ‖D y - D z‖ ≤ C * ‖w - z‖ :=
    (hD y z).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) hC)
  have h := (convex_segment z w).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  have he : (f w - D z w) - (f z - D z z) = f w - f z - D z (w - z) := by
    rw [map_sub]
    ring
  rw [he] at h
  simpa only [pow_two, mul_assoc] using h

theorem metricEntropyPotential_derivative_lipschitz (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z w,
      ‖fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v)) z -
        fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v)) w‖ ≤ C * ‖z - w‖ := by
  have hb (j : Fin n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x z w,
      ‖metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, z) -
        metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, w)‖ ≤ C * ‖z - w‖ := by
    refine (metricEntropyTest_jet_bounds g hη hc Q (EuclideanSpace.single j 1)).elim ?_
    intro C hC
    exact ⟨C, hC.1, hC.2.1⟩
  choose C hC hbound using hb
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC j, ?_⟩
  intro x z w
  apply (covector_norm_le_basis_sum _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  simpa only [sub_apply, metricEntropyPotential_value_test] using hbound j x z w

theorem metricEntropyPotential_quadratic_remainder (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z w,
      ‖metricEntropyPotential g η Q (x, w) - metricEntropyPotential g η Q (x, z) -
        fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v)) z (w - z)‖ ≤
          C * ‖w - z‖ ^ 2 := by
  refine (metricEntropyPotential_derivative_lipschitz g hη hc Q).elim ?_
  intro C hC
  refine ⟨C, hC.1, fun x z w => ?_⟩
  exact quadratic_remainder_of_derivative_lipschitz _ _
    (fun v => (metricEntropyPotential_value_hasFDerivAt g η Q x v).differentiableAt.hasFDerivAt)
    hC.1 (hC.2 x) z w

end PoincareConjecture.M35.Uniqueness.Heat
