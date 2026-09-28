import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderTensorNorm

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.MetricSurgery

theorem cylinder_tensor_weight_lower {r : ℕ} (a : Fin r → Fin 3) :
    (1 / 2 : ℝ) ^ r ≤ ∏ i, cylinderInverseWeight (a i) := by
  calc
    (1 / 2 : ℝ) ^ r = ∏ _i : Fin r, (1 / 2 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun i _ => (cylinderInverseWeight_bounds (a i)).1)

theorem roundCylinderTensorNormSquared_controls_rank_component {r : ℕ}
    (theta : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) (a : Fin r → Fin 3) :
    (T a) ^ 2 ≤ (2 : ℝ) ^ r * roundCylinderTensorNormSquared 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta)
      (chartAt (EuclideanSpace ℝ (Fin 2)) theta theta, s) T := by
  have hweight : (1 / 2 : ℝ) ^ r * (T a) ^ 2 ≤
      roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) theta)
        (chartAt (EuclideanSpace ℝ (Fin 2)) theta theta, s) T := by
    rw [roundCylinderTensorNormSquared_center]
    apply (mul_le_mul_of_nonneg_right (cylinder_tensor_weight_lower a) (sq_nonneg _)).trans
    apply Finset.single_le_sum _ (Finset.mem_univ a)
    intro b _
    exact mul_nonneg
      (Finset.prod_nonneg fun i _ => (by linarith [(cylinderInverseWeight_bounds (b i)).1]))
      (sq_nonneg _)
  calc
    (T a) ^ 2 = (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ r * (T a) ^ 2) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)

theorem roundCylinder_derivative_norm_le_jet (B : RoundCylinderTwoTensor)
    {k order : ℕ} (hk : k ≤ order) (z : RoundCylinderSpace) :
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
        (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)) ≤
      roundCylinderJetErrorSquared 0 B order z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.single_le_sum (f := fun j =>
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B j
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)))
  · intro j _
    exact roundCylinderTensorNormSquared_nonneg z.1 z.2 _
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

theorem roundCylinderClose_derivative_component_sq {epsilon : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (a : Fin (2 + k) → Fin 3) :
    (roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a) ^ 2 ≤
        (2 : ℝ) ^ (2 + k) * epsilon ^ 2 := by
  obtain ⟨bound, hbound, hjet⟩ := hB.2
  exact (roundCylinderTensorNormSquared_controls_rank_component z.1 z.2 _ a).trans
    (mul_le_mul_of_nonneg_left
      ((roundCylinder_derivative_norm_le_jet B hk z).trans ((hjet z hz).trans hbound.le))
      (by positivity))

theorem roundCylinderClose_derivative_component {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (a : Fin (2 + k) → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤
        Real.sqrt ((2 : ℝ) ^ (2 + k)) * epsilon := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hepsilon)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)]
  exact roundCylinderClose_derivative_component_sq hB hk z hz a

theorem roundCylinderClose_first_component {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (horder : 1 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (a : Fin 3 → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 1
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤ 3 * epsilon := by
  have hb := roundCylinderClose_derivative_component_sq hB horder z hz a
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3 * epsilon)).mp
  rw [sq_abs]
  norm_num at hb
  nlinarith [sq_nonneg epsilon]

theorem roundCylinderClose_second_component {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (a : Fin 4 → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 2
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤ 4 * epsilon := by
  have hb := roundCylinderClose_derivative_component_sq hB horder z hz a
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4 * epsilon)).mp
  rw [sq_abs]
  norm_num at hb
  nlinarith

end PoincareConjecture.MetricSurgery
