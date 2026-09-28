import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Determinant










noncomputable section
set_option autoImplicit false

open InnerProductSpace

namespace Poincare.Manifold.SphereIsotopy

private theorem gramSchmidt_inner_self_pos {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin n → E) (hf : LinearIndependent ℝ f) (i : Fin n) :
    0 < inner ℝ (gramSchmidtNormed ℝ f i) (f i) := by
  have hn : 0 < ‖gramSchmidt ℝ f i‖ :=
    norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)
  have hinner : inner ℝ (gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖ ^ 2 := by
    calc
      inner ℝ (gramSchmidt ℝ f i) (f i) =
          inner ℝ (gramSchmidt ℝ f i)
            (gramSchmidt ℝ f i + ∑ j ∈ Finset.Iio i,
              (inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖ ^ 2) •
                gramSchmidt ℝ f j) :=
        congrArg (inner ℝ (gramSchmidt ℝ f i)) (gramSchmidt_def'' ℝ f i)
      _ = ‖gramSchmidt ℝ f i‖ ^ 2 := by
        rw [inner_add_right, inner_sum]
        have hz : ∑ j ∈ Finset.Iio i,
            inner ℝ (gramSchmidt ℝ f i)
              ((inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖ ^ 2) •
                gramSchmidt ℝ f j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp only [inner_smul_right,
            gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.mp hj).ne', mul_zero]
        rw [hz, add_zero, real_inner_self_eq_norm_sq]
  rw [gramSchmidtNormed, real_inner_smul_left, hinner]
  exact mul_pos (inv_pos.mpr hn) (sq_pos_of_pos hn)



theorem exists_orthogonal_linear_interpolation {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Function.Bijective
          ((1 - t) • L.toContinuousLinearMap +
            t • Q.toContinuousLinearEquiv.toContinuousLinearMap) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let f : Fin n → EuclideanSpace ℝ (Fin n) := fun i => L (b i)
  have hf : LinearIndependent ℝ f := (b.toBasis.map L.toLinearEquiv).linearIndependent
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  let c := gramSchmidtOrthonormalBasis hdim f
  let Q := b.equiv c (Equiv.refl (Fin n))
  have hQ (i : Fin n) : Q (b i) = c i := by simp [Q]
  have hc (i : Fin n) : 0 < inner ℝ (c i) (f i) := by
    have hn : gramSchmidtNormed ℝ f i ≠ 0 := by
      intro hz
      have := gramSchmidtNormed_unit_length i hf
      rw [hz, norm_zero] at this
      exact zero_ne_one this
    rw [show c i = gramSchmidtNormed ℝ f i from
      gramSchmidtOrthonormalBasis_apply hdim hn]
    exact gramSchmidt_inner_self_pos f hf i
  refine ⟨Q, fun t ht => ?_⟩
  let A := (1 - t) • L.toContinuousLinearMap +
    t • Q.toContinuousLinearEquiv.toContinuousLinearMap
  let M := LinearMap.toMatrix b.toBasis c.toBasis A.toLinearMap
  have hM (i j : Fin n) : M i j =
      (1 - t) * inner ℝ (c i) (f j) + t * inner ℝ (c i) (c j) := by
    simp [M, A, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, hQ, f, orthonormal_iff_ite.mp c.orthonormal]
  have htri : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    have hz : inner ℝ (c i) (f j) = 0 :=
      gramSchmidtOrthonormalBasis_inv_triangular hdim f hji
    rw [hM, hz, c.orthonormal.2 hji.ne', mul_zero, mul_zero, add_zero]
  have hdiag (i : Fin n) : 0 < M i i := by
    rw [hM, real_inner_self_eq_norm_sq, c.orthonormal.1 i, one_pow, mul_one]
    have hnonneg : 0 ≤ (1 - t) * inner ℝ (c i) (f i) :=
      mul_nonneg (sub_nonneg.mpr ht.2) (hc i).le
    rcases ht.1.eq_or_lt with hzero | hpos
    · rw [← hzero]
      simpa using hc i
    · exact add_pos_of_nonneg_of_pos hnonneg hpos
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hdiag i).ne'
  exact (LinearEquiv.ofIsUnitDet hdet).bijective

end Poincare.Manifold.SphereIsotopy
