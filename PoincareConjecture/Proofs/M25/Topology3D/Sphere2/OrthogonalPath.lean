import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open scoped ContDiff
open InnerProductSpace Module

namespace PoincareConjecture.M25.Topology3D

private theorem gramSchmidt_diagonal_pos (v : Basis (Fin 3) ℝ E3) (i : Fin 3) :
    0 < inner ℝ (gramSchmidtOrthonormalBasis
      (by simp : Module.finrank ℝ E3 = Fintype.card (Fin 3)) v i) (v i) := by
  have hw : 0 < ‖gramSchmidt ℝ v i‖ := norm_pos_iff.mpr
    (gramSchmidt_ne_zero i v.linearIndependent)
  have hn : gramSchmidtNormed ℝ v i ≠ 0 := by
    intro h
    have := gramSchmidtNormed_unit_length i v.linearIndependent
    rw [h, norm_zero] at this
    norm_num at this
  have hdiag : inner ℝ (gramSchmidt ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ ^ 2 := by
    calc
      inner ℝ (gramSchmidt ℝ v i) (v i) =
          inner ℝ (gramSchmidt ℝ v i) (gramSchmidt ℝ v i +
            ∑ j ∈ Finset.Iio i,
              (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖ ^ 2) •
                gramSchmidt ℝ v j) :=
        congrArg (inner ℝ (gramSchmidt ℝ v i)) (gramSchmidt_def'' ℝ v i)
      _ = ‖gramSchmidt ℝ v i‖ ^ 2 := by
        rw [inner_add_right, inner_sum]
        have hs : (∑ j ∈ Finset.Iio i,
            inner ℝ (gramSchmidt ℝ v i)
              ((inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖ ^ 2) •
                gramSchmidt ℝ v j)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [inner_smul_right, gramSchmidt_orthogonal ℝ v
            (ne_of_gt (Finset.mem_Iio.mp hj)), mul_zero]
        rw [hs, add_zero, real_inner_self_eq_norm_sq]
  rw [gramSchmidtOrthonormalBasis_apply (by simp) hn, gramSchmidtNormed,
    real_inner_smul_left, hdiag]
  exact mul_pos (inv_pos.mpr hw) (sq_pos_of_pos hw)

theorem exists_orthogonal_linear_path (L : E3 ≃L[ℝ] E3) :
    ∃ A : E3 ≃ₗᵢ[ℝ] E3, ∃ H : ℝ → E3 ≃L[ℝ] E3,
      ContDiff ℝ ∞ (fun p : ℝ × E3 => H p.1 p.2) ∧
      (∀ t x, H t x = (1 - Real.smoothTransition t) • L x +
        Real.smoothTransition t • A x) ∧
      (∀ t, t ≤ 0 → ∀ x, H t x = L x) ∧
      (∀ t, 1 ≤ t → ∀ x, H t x = A x) := by
  classical
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let v : Basis (Fin 3) ℝ E3 := b.toBasis.map L.toLinearEquiv
  let c := gramSchmidtOrthonormalBasis (by simp : Module.finrank ℝ E3 =
    Fintype.card (Fin 3)) v
  let A : E3 ≃ₗᵢ[ℝ] E3 := b.equiv c (Equiv.refl (Fin 3))
  let T (t : ℝ) : E3 →L[ℝ] E3 :=
    (1 - Real.smoothTransition t) • (L : E3 →L[ℝ] E3) +
      Real.smoothTransition t • A.toContinuousLinearEquiv.toContinuousLinearMap
  let M (t : ℝ) := LinearMap.toMatrix b.toBasis c.toBasis (T t).toLinearMap
  have hentry (t : ℝ) (i j : Fin 3) : M t i j =
      (1 - Real.smoothTransition t) * c.repr (v j) i +
        Real.smoothTransition t * (if i = j then 1 else 0) := by
    simp [M, LinearMap.toMatrix_apply, T, v, A]
  have hdiag (i : Fin 3) : 0 < c.repr (v i) i := by
    rw [OrthonormalBasis.repr_apply_apply]
    exact gramSchmidt_diagonal_pos v i
  have hdet (t : ℝ) : IsUnit (M t).det := by
    have htri : (M t).IsUpperTriangular := by
      intro i j hij
      change j < i at hij
      have hcij : c.repr (v j) i = 0 := gramSchmidtOrthonormalBasis_inv_triangular'
        (by simp : Module.finrank ℝ E3 = Fintype.card (Fin 3)) v (show j < i from hij)
      rw [hentry, hcij,
        if_neg (ne_of_gt hij), mul_zero, mul_zero, add_zero]
    have hd (i : Fin 3) : 0 < M t i i := by
      rw [hentry, if_pos rfl, mul_one]
      by_cases h : Real.smoothTransition t = 1
      · rw [h]
        norm_num
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr (lt_of_le_of_ne (Real.smoothTransition.le_one t) h))
            (hdiag i)) (Real.smoothTransition.nonneg t)
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_of_isUpperTriangular htri]
    exact ne_of_gt (Finset.prod_pos fun i _ => hd i)
  let H (t : ℝ) : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.ofIsUnitDet (hdet t)).toContinuousLinearEquiv
  have hformula (t : ℝ) (x : E3) : H t x =
      (1 - Real.smoothTransition t) • L x + Real.smoothTransition t • A x := rfl
  refine ⟨A, H, ?_, hformula, ?_, ?_⟩
  · have heq : (fun p : ℝ × E3 => H p.1 p.2) =
        (fun p : ℝ × E3 => (1 - Real.smoothTransition p.1) • L p.2 +
          Real.smoothTransition p.1 • A p.2) := funext fun p => hformula p.1 p.2
    rw [heq]
    exact ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).smul
      (L.contDiff.comp contDiff_snd)).add
        ((Real.smoothTransition.contDiff.comp contDiff_fst).smul
          (A.toContinuousLinearEquiv.contDiff.comp contDiff_snd))
  · intro t ht x
    rw [hformula, Real.smoothTransition.zero_of_nonpos ht]
    simp
  · intro t ht x
    rw [hformula, Real.smoothTransition.one_of_one_le ht]
    simp

end PoincareConjecture.M25.Topology3D
