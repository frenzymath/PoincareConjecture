import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderGram
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring









set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.MetricSurgery

noncomputable def cylinderInverseWeight : Fin 3 → ℝ := ![1 / 2, 1 / 2, 1]

theorem cylinderInverseWeight_bounds (i : Fin 3) :
    1 / 2 ≤ cylinderInverseWeight i ∧ cylinderInverseWeight i ≤ 1 := by
  fin_cases i <;> norm_num [cylinderInverseWeight]

theorem diagonal_tensor_product {r : ℕ} (d : Fin 3 → ℝ) (a b : Fin r → Fin 3) :
    (∏ i, Matrix.diagonal d (a i) (b i)) = if a = b then ∏ i, d (a i) else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [Matrix.diagonal]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal, hi])

theorem roundCylinderTensorNormSquared_center {r : ℕ}
    (theta : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) theta)
        (chartAt (EuclideanSpace ℝ (Fin 2)) theta theta, s) T =
      ∑ a, (∏ i, cylinderInverseWeight (a i)) * (T a) ^ 2 := by
  classical
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_center_inv]
  change (∑ a, ∑ b, (∏ i, Matrix.diagonal cylinderInverseWeight (a i) (b i)) * T a * T b) = _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · rw [diagonal_tensor_product, if_pos rfl]
    ring
  · intro b _ hba
    rw [diagonal_tensor_product, if_neg (Ne.symm hba), zero_mul, zero_mul]
  · simp

theorem roundCylinderTensorNormSquared_nonneg {r : ℕ}
    (theta : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta)
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta theta, s) T := by
  rw [roundCylinderTensorNormSquared_center]
  exact Finset.sum_nonneg fun a _ => mul_nonneg
    (Finset.prod_nonneg fun i _ => (by linarith [(cylinderInverseWeight_bounds (a i)).1]))
    (sq_nonneg _)

theorem cylinder_rank_two_weight_lower (a : Fin 2 → Fin 3) :
    (1 / 4 : ℝ) ≤ ∏ i, cylinderInverseWeight (a i) := by
  rw [Fin.prod_univ_two]
  have h₀ := (cylinderInverseWeight_bounds (a 0)).1
  have h₁ := (cylinderInverseWeight_bounds (a 1)).1
  nlinarith

theorem roundCylinderTensorNormSquared_controls_component
    (theta : UnitTwoSphere) (s : ℝ) (T : (Fin 2 → Fin 3) → ℝ) (a : Fin 2 → Fin 3) :
    (1 / 4 : ℝ) * (T a) ^ 2 ≤ roundCylinderTensorNormSquared 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta)
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta theta, s) T := by
  rw [roundCylinderTensorNormSquared_center]
  apply (mul_le_mul_of_nonneg_right (cylinder_rank_two_weight_lower a) (sq_nonneg _)).trans
  apply Finset.single_le_sum _ (Finset.mem_univ a)
  intro b _
  exact mul_nonneg
    (Finset.prod_nonneg fun i _ => (by linarith [(cylinderInverseWeight_bounds (b i)).1]))
    (sq_nonneg _)

theorem roundCylinder_component_le_sqrt_norm
    (theta : UnitTwoSphere) (s : ℝ) (T : (Fin 2 → Fin 3) → ℝ) (a : Fin 2 → Fin 3) :
    |T a| ≤ 2 * Real.sqrt (roundCylinderTensorNormSquared 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta)
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta theta, s) T) := by
  have hn := roundCylinderTensorNormSquared_nonneg theta s T
  have hbound := roundCylinderTensorNormSquared_controls_component theta s T a
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hn]
  nlinarith

theorem roundCylinderJetErrorSquared_nonneg (B : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) : 0 ≤ roundCylinderJetErrorSquared 0 B order z := by
  unfold roundCylinderJetErrorSquared
  exact Finset.sum_nonneg fun k _ => roundCylinderTensorNormSquared_nonneg z.1 z.2 _

theorem roundCylinder_zero_norm_le_jet (B : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) ≤
      roundCylinderJetErrorSquared 0 B order z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.single_le_sum (f := fun k =>
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)))
  · intro k _
    exact roundCylinderTensorNormSquared_nonneg z.1 z.2 _
  · exact Finset.mem_range.mpr (Nat.zero_lt_succ order)

theorem roundCylinder_coefficient_error_le (B : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) (a b : Fin 3) :
    |roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a b -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a b| ≤
      2 * Real.sqrt (roundCylinderJetErrorSquared 0 B order z) := by
  have h := roundCylinder_component_le_sqrt_norm z.1 z.2
    (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) ![a, b]
  apply le_trans ?_
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (roundCylinder_zero_norm_le_jet B order z))
      (by norm_num))
  simpa only [roundCylinderIteratedDerivative, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h

theorem roundCylinderClose_coefficient_error {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (a b : Fin 3) :
    |roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a b -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a b| ≤ 2 * epsilon := by
  obtain ⟨bound, hbound, hjet⟩ := hB.2
  have hsqrt := Real.sqrt_le_sqrt ((hjet z hz).trans hbound.le)
  rw [Real.sqrt_sq hepsilon.le] at hsqrt
  exact (roundCylinder_coefficient_error_le B _ z a b).trans
    (mul_le_mul_of_nonneg_left hsqrt (by norm_num))

end PoincareConjecture.MetricSurgery
