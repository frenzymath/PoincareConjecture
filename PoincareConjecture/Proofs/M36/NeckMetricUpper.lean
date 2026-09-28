import PoincareConjecture.Proofs.M36.NeckMetricBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture.M36

local notation "C" => RoundCylinderCoordinates

theorem cylinder_bilinear_error_bound (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (B : C →L[ℝ] C →L[ℝ] ℝ)
    (hB : ∀ i j, |B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
      Matrix.diagonal ![(2 : ℝ), 2, 1] i j| ≤ 2 * epsilon) (v : C) :
    |B v v - (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2)| ≤
      6 * epsilon * (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2) := by
  have h := cylinder_matrix_quadratic_bound epsilon hepsilon
    (fun i j => B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
      Matrix.diagonal ![(2 : ℝ), 2, 1] i j) hB (cylinderComponents v)
  have heq : (∑ i : Fin 3, ∑ j : Fin 3, cylinderComponents v i * cylinderComponents v j *
      (B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
        Matrix.diagonal ![(2 : ℝ), 2, 1] i j)) =
      B v v - (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2) := by
    rw [cylinder_bilinear_expansion]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp [Fin.sum_univ_three, cylinderComponents, Matrix.diagonal]
    ring
  rw [heq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 6 * epsilon)
  rw [Fin.sum_univ_three]
  change (v.1 0) ^ 2 + (v.1 1) ^ 2 + v.2 ^ 2 ≤
    2 * ((v.1 0) ^ 2 + (v.1 1) ^ 2) + v.2 ^ 2
  nlinarith [sq_nonneg (v.1 0), sq_nonneg (v.1 1)]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem normalizedNeck_bounded_above (N : EpsilonNeck g) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : C) :
    N.connection.scalarCurvature N.center * roundCylinderPullback g N.coordinate_map z v v ≤
      (1 + 6 * N.epsilon) * RoundCylinderMetric z v v := by
  have hcoeff (i j : Fin 3) :
      |normalizedNeckForm N z (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
        Matrix.diagonal ![(2 : ℝ), 2, 1] i j| ≤ 2 * N.epsilon := by
    have h := roundCylinderClose_coefficient_error N.epsilon_pos N.metric_comparison.close z hz i j
    rw [roundCylinderTensorCoefficient_center, roundCylinderGram_center] at h
    exact h
  have h := (abs_le.mp
    (cylinder_bilinear_error_bound N.epsilon N.epsilon_pos.le (normalizedNeckForm N z) hcoeff v)).2
  rw [normalizedNeckForm_apply] at h
  rw [roundCylinderMetric_quadratic]
  nlinarith

end PoincareConjecture.M36
