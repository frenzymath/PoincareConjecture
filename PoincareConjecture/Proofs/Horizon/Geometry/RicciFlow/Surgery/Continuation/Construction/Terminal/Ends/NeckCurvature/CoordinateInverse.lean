import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.ModelJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Dual

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.RiemannianMetric

theorem inverseCoefficients_eq_inverse_gram_standard {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.of (g.inverseCoefficients x) =
      (Matrix.of (fun i j => g.inner x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  ext i j
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let v : EuclideanSpace ℝ (Fin n) := (g.inner x).inverse (EuclideanSpace.proj j)
  have hsum := congrArg (g.inner x (e i)) (e.toBasis.sum_repr v)
  simp only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply] at hsum
  simp only [e, EuclideanSpace.basisFun_repr] at hsum
  have hv : g.inner x (e i) v = EuclideanSpace.proj j (e i) := by
    rw [g.symm]
    exact congrArg (fun L => L (e i))
      ((g.inner_isInvertible x).self_apply_inverse (EuclideanSpace.proj j))
  rw [hv] at hsum
  change (∑ k, g.inner x (e i) (e k) * g.inverseCoefficients x k j) = _
  simp_rw [g.inverseCoefficients_symm x _ j]
  change (∑ k, g.inner x (e i) (e k) * v k) = _
  rw [show (∑ k, g.inner x (e i) (e k) * v k) =
    ∑ k, v k * g.inner x (e i) (e k) by simp only [mul_comm], hsum]
  simp [e, EuclideanSpace.basisFun_apply, PiLp.single_apply, Matrix.one_apply, eq_comm]

theorem inverseCoefficients_eq_cylinder_inverse_gram
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    g.inverseCoefficients x ((finRotate 3) i) ((finRotate 3) j) =
      (Matrix.of (fun i j => g.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)))⁻¹ i j := by
  have hG : Matrix.of (fun i j => g.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)) =
      (Matrix.of (fun i j => g.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j))).submatrix (finRotate 3) (finRotate 3) := by
    ext a b
    simp only [roundCylinderEuclideanBasis, Module.Basis.reindex_apply,
      Equiv.symm_symm, OrthonormalBasis.coe_toBasis, Matrix.of_apply, Matrix.submatrix_apply]
  rw [hG, Matrix.inv_submatrix_equiv, ← g.inverseCoefficients_eq_inverse_gram_standard x]
  rfl

theorem sum_abs_inverseCoefficients_eq_cylinder_inverse_gram
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    (∑ i, ∑ j, |g.inverseCoefficients x i j|) =
      ∑ i, ∑ j, |(Matrix.of (fun i j => g.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)))⁻¹ i j| := by
  simp_rw [← g.inverseCoefficients_eq_cylinder_inverse_gram x]
  calc
    _ = ∑ i, ∑ j, |g.inverseCoefficients x i ((finRotate 3) j)| := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Equiv.sum_comp (finRotate 3) (fun j => |g.inverseCoefficients x i j|)).symm
    _ = _ := (Equiv.sum_comp (finRotate 3)
      (fun i => ∑ j, |g.inverseCoefficients x i ((finRotate 3) j)|)).symm

end PoincareConjecture.RiemannianMetric
