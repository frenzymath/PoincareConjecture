import PoincareConjecture.Proofs.M36.CylinderTensorNorm
import PoincareConjecture.Proofs.M36.NeckCoordinates
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "C" => RoundCylinderCoordinates

set_option backward.isDefEq.respectTransparency false in
theorem sphere_chart_inverse_mfderiv (theta : UnitTwoSphere) :
    mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm (chartAt E₂ theta theta) =
      ContinuousLinearMap.id ℝ E₂ := by
  convert! (mfderivWithin_range_extChartAt_symm (I := 𝓡 2) (x := theta)) using 1
  simp

set_option backward.isDefEq.respectTransparency false in
theorem roundCylinderTensorCoefficient_center (B : RoundCylinderTwoTensor)
    (z : RoundCylinderSpace) (a b : Fin 3) :
    roundCylinderTensorCoefficient B (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2) a b =
      B z (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b) := by
  unfold roundCylinderTensorCoefficient
  rw [sphere_chart_inverse_mfderiv]
  change B ((chartAt E₂ z.1).symm (chartAt E₂ z.1 z.1), z.2)
    (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b) = _
  congr 1
  exact Prod.ext ((chartAt E₂ z.1).left_inv (mem_chart_source E₂ z.1)) rfl

set_option backward.isDefEq.respectTransparency false in
theorem sphere_inclusion_inner (theta : UnitTwoSphere) (v w : E₂) :
    inner ℝ (E := EuclideanSpace ℝ (Fin 3))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) theta v)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) theta w) = inner ℝ v w := by
  have h := sphere_chart_differential_inner theta v w
  have hzero : (chartAt E₂ theta).symm 0 = theta := by
    rw [← sphere_chart_center_zero theta]
    exact (chartAt E₂ theta).left_inv (mem_chart_source E₂ theta)
  have hderiv : mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm 0 =
      ContinuousLinearMap.id ℝ E₂ := by
    convert! sphere_chart_inverse_mfderiv theta using 1
    rw [sphere_chart_center_zero]
  rw [hderiv] at h
  change inner ℝ (E := EuclideanSpace ℝ (Fin 3))
    (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
      ((chartAt E₂ theta).symm 0) v)
    (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
      ((chartAt E₂ theta).symm 0) w) = inner ℝ v w at h
  convert! h using 1
  rw [hzero]

set_option backward.isDefEq.respectTransparency false in
theorem roundCylinderMetric_quadratic (z : RoundCylinderSpace) (v : C) :
    RoundCylinderMetric z v v = 2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2 := by
  change 2 * (1 - (0 : ℝ)) * inner ℝ (E := EuclideanSpace ℝ (Fin 3))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) z.1 v.1)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) z.1 v.1) + v.2 * v.2 = _
  rw [sphere_inclusion_inner]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial, sub_zero, mul_one, pow_two]

def cylinderComponents (v : C) : Fin 3 → ℝ := ![v.1 0, v.1 1, v.2]

theorem cylinder_basis_expansion (v : C) :
    ∑ i : Fin 3, cylinderComponents v i • roundCylinderCoordinateBasis i = v := by
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [Fin.sum_univ_three, cylinderComponents, roundCylinderCoordinateBasis,
        EuclideanSpace.basisFun, LinearIsometryEquiv.symm, LinearIsometryEquiv.refl]
  · simp [Fin.sum_univ_three, cylinderComponents, roundCylinderCoordinateBasis]

theorem cylinder_bilinear_expansion (B : C →L[ℝ] C →L[ℝ] ℝ) (v : C) :
    B v v = ∑ i : Fin 3, ∑ j : Fin 3,
      cylinderComponents v i * cylinderComponents v j *
        B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) := by
  calc
    B v v = B (∑ i : Fin 3, cylinderComponents v i • roundCylinderCoordinateBasis i)
        (∑ j : Fin 3, cylinderComponents v j • roundCylinderCoordinateBasis j) := by
      rw [cylinder_basis_expansion]
    _ = _ := by
      simp only [Fin.sum_univ_three, map_add, map_smul,
        add_apply, smul_apply, smul_eq_mul]
      ring

theorem cylinder_matrix_quadratic_bound (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j, |A i j| ≤ 2 * epsilon)
    (v : Fin 3 → ℝ) :
    |∑ i : Fin 3, ∑ j : Fin 3, v i * v j * A i j| ≤
      6 * epsilon * ∑ i : Fin 3, v i ^ 2 := by
  have hCS : (∑ i : Fin 3, |v i|) ^ 2 ≤ 3 * ∑ i : Fin 3, v i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun i => |v i|) (fun _ => (1 : ℝ))
    norm_num only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h
    nlinarith [h]
  calc
    |∑ i : Fin 3, ∑ j : Fin 3, v i * v j * A i j| ≤
        ∑ i : Fin 3, ∑ j : Fin 3, |v i| * |v j| * |A i j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun j : Fin 3 => v i * v j * A i j) Finset.univ)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |v i| * |v j| * (2 * epsilon) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hA i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (2 * epsilon) * (∑ i : Fin 3, |v i|) ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
    _ ≤ (2 * epsilon) * (3 * ∑ i : Fin 3, v i ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (mul_nonneg (by norm_num) hepsilon)
    _ = _ := by ring

theorem cylinder_bilinear_lower_bound (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (B : C →L[ℝ] C →L[ℝ] ℝ)
    (hB : ∀ i j, |B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
      Matrix.diagonal ![(2 : ℝ), 2, 1] i j| ≤ 2 * epsilon) (v : C) :
    (1 - 6 * epsilon) * (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2) ≤ B v v := by
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
  have hs : (∑ i : Fin 3, cylinderComponents v i ^ 2) ≤
      2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2 := by
    rw [Fin.sum_univ_three]
    change (v.1 0) ^ 2 + (v.1 1) ^ 2 + v.2 ^ 2 ≤
      2 * ((v.1 0) ^ 2 + (v.1 1) ^ 2) + v.2 ^ 2
    nlinarith [sq_nonneg (v.1 0), sq_nonneg (v.1 1)]
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6 * epsilon by positivity)
  have hlo := (abs_le.mp h).1
  nlinarith

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem neck_scale_inverse_sq (N : EpsilonNeck g) :
    N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
  rw [N.scale_eq_scalar, inv_pow,
    ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2) 2]
  norm_num [Real.rpow_neg_one]

noncomputable def normalizedNeckForm (N : EpsilonNeck g) (z : RoundCylinderSpace) :
    C →L[ℝ] C →L[ℝ] ℝ :=
  let D := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
  N.scale⁻¹ ^ 2 • (D.precomp ℝ).comp ((g.inner (N.coordinate_map z)).comp D)

theorem normalizedNeckForm_apply (N : EpsilonNeck g) (z : RoundCylinderSpace) (v w : C) :
    normalizedNeckForm N z v w = N.connection.scalarCurvature N.center *
      roundCylinderPullback g N.coordinate_map z v w := by
  change N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w = _
  rw [neck_scale_inverse_sq]

theorem normalizedNeckForm_lower (N : EpsilonNeck g) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : C) :
    (1 - 6 * N.epsilon) * (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2) ≤
      normalizedNeckForm N z v v := by
  apply cylinder_bilinear_lower_bound N.epsilon N.epsilon_pos.le
  intro i j
  have h := roundCylinderClose_coefficient_error N.epsilon_pos N.metric_comparison.close z hz i j
  rw [roundCylinderTensorCoefficient_center, roundCylinderGram_center] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem normalizedNeck_dominates_cylinder (N : EpsilonNeck g) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : RoundCylinderTangent z) :
    (1 - 6 * N.epsilon) * RoundCylinderMetric z v v ≤
      N.connection.scalarCurvature N.center * roundCylinderPullback g N.coordinate_map z v v := by
  calc
    _ = (1 - 6 * N.epsilon) * (2 * (v.1 0 ^ 2 + v.1 1 ^ 2) + v.2 ^ 2) := by
      congr 1
      exact roundCylinderMetric_quadratic z v
    _ ≤ normalizedNeckForm N z v v := normalizedNeckForm_lower N z hz v
    _ = _ := normalizedNeckForm_apply N z v v

theorem neck_contraction_coefficient_pos (N : EpsilonNeck g)
    (hsmall : N.epsilon < 1 / 200) : 0 < 1 - 6 * N.epsilon := by
  linarith

end PoincareConjecture.M36
