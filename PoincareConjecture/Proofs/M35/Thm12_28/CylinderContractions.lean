import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCurvature
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetNorm
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence
import PoincareConjecture.Proofs.M13.CurvatureContractions

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

private theorem cylinder_gram_center (u : ℝ) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) :
    Matrix.of (fun i j : Fin 3 => (cylinderEuclideanMetric u hu).inner
      (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) := by
  ext i j
  have h := cylinderEuclideanMetric_basis u hu q
    (cylinderCoordinateEquiv.symm (0, s)) i j
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [sphere_chart_center]
  exact h

theorem cylinder_ricci_center (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (s : ℝ) (i j : Fin 3) :
    D.ricci (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1 := by
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor p
  have hr := D.ricci_eq_inverse_gram p (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis A hA
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
  refine Eq.trans (by exact hr) ?_
  change (∑ a : Fin 3, ∑ b : Fin 3,
    (Matrix.of (fun a b : Fin 3 => (cylinderEuclideanMetric u hu).inner
      (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)))⁻¹ a b *
    D.curvatureTensor (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ b)) = _
  rw [cylinder_gram_center u hu q s, roundCylinderGram_inv_center hu]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp_rw [cylinder_curvatureTensor_center u hu D q]
  have ht : 1 - u ≠ 0 := by linarith
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, roundCylinderCoordinateBasis,
      EuclideanSpace.inner_single_left] <;> field_simp [ht]

theorem cylinder_scalarCurvature_center (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (s : ℝ) :
    D.scalarCurvature (cylinderCoordinateEquiv.symm (0, s)) = 1 / (1 - u) := by
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : EuclideanSpace ℝ (Fin 3) → Type _) :=
    ⟨(cylinderEuclideanMetric u hu).toRiemannianMetric⟩
  have h := bilinear_sum_basis_eq_inverse_gram (M13.ricciLinear D p)
    (show Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) p) from
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
    ((cylinderEuclideanMetric u hu).orthonormalBasis p)
  change D.scalarCurvature p = ∑ i : Fin 3, ∑ j : Fin 3,
    (Matrix.of (fun i j : Fin 3 => (cylinderEuclideanMetric u hu).inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)))⁻¹ i j *
      D.ricci p (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) at h
  refine Eq.trans (by exact h) ?_
  change (∑ i : Fin 3, ∑ j : Fin 3,
    (Matrix.of (fun i j : Fin 3 => (cylinderEuclideanMetric u hu).inner
      (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)))⁻¹ i j *
      D.ricci (cylinderCoordinateEquiv.symm (0, s)) (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [cylinder_gram_center u hu q s, roundCylinderGram_inv_center hu]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp_rw [cylinder_ricci_center u hu D q]
  norm_num [Fin.sum_univ_succ, roundCylinderCoordinateBasis,
    EuclideanSpace.inner_single_left]
  ring

private theorem sum_fin_tuple_succ {r : ℕ} (f : (Fin (r + 1) → Fin 3) → ℝ) :
    (∑ a : Fin (r + 1) → Fin 3, f a) =
      ∑ i : Fin 3, ∑ a : Fin r → Fin 3, f (Fin.cons i a) := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin 3))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm

private theorem sum_four_tuple (f : (Fin 4 → Fin 3) → ℝ) :
    (∑ a : Fin 4 → Fin 3, f a) = ∑ i : Fin 3, ∑ j : Fin 3,
      ∑ k : Fin 3, ∑ l : Fin 3, f ![i, j, k, l] := by
  simp_rw [sum_fin_tuple_succ]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  congr 1

theorem cylinder_curvatureTensorNorm_center (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (s : ℝ) :
    D.curvatureTensorNorm (cylinderCoordinateEquiv.symm (0, s)) = 1 / (1 - u) := by
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let T : (Fin 4 → Fin 3) → ℝ := fun a => D.curvatureTensor p
    (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)) (EuclideanSpace.basisFun (Fin 3) ℝ (a 1))
    (EuclideanSpace.basisFun (Fin 3) ℝ (a 2)) (EuclideanSpace.basisFun (Fin 3) ℝ (a 3))
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor p
  have hn := D.curvatureTensorNorm_eq_tensorNormFromComponents p
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis A hA
  have hc : D.curvatureTensorNorm p = Real.sqrt
      (roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T) := by
    refine Eq.trans hn ?_
    change tensorNormFromComponents (Matrix.of (fun i j : Fin 3 =>
      (cylinderEuclideanMetric u hu).inner (cylinderCoordinateEquiv.symm (0, s))
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))) T = _
    rw [cylinder_gram_center u hu q s]
    simp only [tensorNormFromComponents, roundCylinderTensorNormSquared, mul_assoc]
  refine Eq.trans (by exact hc) ?_
  rw [roundCylinderTensorNormSquared_center hu]
  have hs : (∑ a : Fin 4 → Fin 3,
      (∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i)) * (T a) ^ 2) =
        (1 / (1 - u)) ^ 2 := by
    rw [sum_four_tuple]
    simp only [T, p, cylinder_curvatureTensor_center u hu D q]
    norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, roundCylinderCoordinateBasis,
      Matrix.cons_val_two, Matrix.cons_val_three, EuclideanSpace.inner_single_left]
    have ht : 1 - u ≠ 0 := by linarith
    field_simp [ht]
    ring
  rw [hs, Real.sqrt_sq (le_of_lt (one_div_pos.mpr (sub_pos.mpr hu)))]

end PoincareConjecture.M35
