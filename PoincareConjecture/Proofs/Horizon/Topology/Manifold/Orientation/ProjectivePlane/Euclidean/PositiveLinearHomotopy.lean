import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring








set_option autoImplicit false

open scoped unitInterval Matrix

namespace Poincare.Topology

theorem exists_positive_linear_puncture_homotopy
    (L : EuclideanSpace Real (Fin 3) ≃L[Real] EuclideanSpace Real (Fin 3))
    (hL : 0 < L.toLinearEquiv.toLinearMap.det) :
    ∃ H : ContinuousMap.Homotopy
      (ContinuousMap.id (EuclideanSpace Real (Fin 3)))
      (⟨L, L.continuous⟩ :
        C(EuclideanSpace Real (Fin 3), EuclideanSpace Real (Fin 3))),
      ∀ t : unitInterval,
        Set.MapsTo (fun x => H (t, x)) ({0}ᶜ : Set (EuclideanSpace Real (Fin 3)))
          ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) := by
  classical
  let G := Matrix.SpecialLinearGroup (Fin 3) Real
  have shear (i j : Fin 3) (hij : i ≠ j) (a : Real) :
      Joined (1 : G) (Matrix.SpecialLinearGroup.transvection hij a) := by
    refine ⟨{ toFun := fun t => Matrix.SpecialLinearGroup.transvection hij ((t : Real) * a)
              continuous_toFun := ?_
              source' := by simp
              target' := by simp }⟩
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval =>
      (1 : Matrix (Fin 3) (Fin 3) Real) + Matrix.single i j ((t : Real) * a))
    apply continuous_pi
    intro k
    apply continuous_pi
    intro l
    simp only [Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  have multiply (A B : G) (hA : Joined 1 A) (hB : Joined 1 B) :
      Joined 1 (A * B) := by
    simpa only [one_mul] using hA.mul hB
  have diagonal (i j : Fin 3) (hij : i ≠ j) (c : Real) (hc : c ≠ 0) :
      Joined (1 : G) (Matrix.SpecialLinearGroup.diag2n hij c hc) := by
    have factor : Matrix.SpecialLinearGroup.diag2n hij c hc =
        Matrix.SpecialLinearGroup.transvection hij c *
        Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
        Matrix.SpecialLinearGroup.transvection hij c *
        Matrix.SpecialLinearGroup.transvection hij (-1) *
        Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.diag2n_coe]
      ext k l
      simp only [mul_add, add_mul, one_mul, mul_one,
        Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hij,
        Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, add_zero]
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
        simp_all [Matrix.diagonal_apply, Matrix.single_apply, Matrix.one_apply, eq_comm]
    rw [factor]
    exact multiply _ _ (multiply _ _ (multiply _ _ (multiply _ _
      (multiply _ _ (shear i j hij c) (shear j i hij.symm (-c⁻¹)))
      (shear i j hij c)) (shear i j hij (-1))) (shear j i hij.symm 1))
      (shear i j hij (-1))
  have connected (A : G) : Joined (1 : G) A := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun B : G => Joined 1 B) A
    · intro i j hij c hc
      exact diagonal i j hij c hc
    · exact shear
    · exact multiply
  let b := (EuclideanSpace.basisFun (Fin 3) Real).toBasis
  let e := b.equivFun.toContinuousLinearEquiv
  let M := LinearMap.toMatrix b b L.toLinearEquiv.toLinearMap
  let d := M.det
  have hd : 0 < d := by
    simpa only [d, M, LinearMap.det_toMatrix] using hL
  let D (a : Real) : Matrix (Fin 3) (Fin 3) Real :=
    Matrix.diagonal (fun i => if i = 0 then a else 1)
  have detD (a : Real) : (D a).det = a := by
    simp [D, Matrix.det_diagonal]
  have D_one : D 1 = 1 := by simp [D]
  have D_mul (a c : Real) : D a * D c = D (a * c) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  let A : G := ⟨D d⁻¹ * M, by
    rw [Matrix.det_mul, detD]
    exact inv_mul_cancel₀ (ne_of_gt hd)⟩
  let p := (connected A).somePath
  let P (t : unitInterval) : Matrix (Fin 3) (Fin 3) Real :=
    D (1 - (t : Real) + (t : Real) * d) * (p t).val
  have P_continuous : Continuous P := by
    have hD : Continuous (fun t : unitInterval => D (1 - (t : Real) + (t : Real) * d)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      simp only [D, Matrix.diagonal_apply]
      split_ifs <;> fun_prop
    exact hD.mul (continuous_subtype_val.comp p.continuous)
  have P_zero : P 0 = 1 := by simp [P, p, D_one]
  have P_one : P 1 = M := by
    change D (1 - (1 : Real) + 1 * d) * (p 1).val = M
    simp only [sub_self, one_mul, zero_add, Path.target]
    change D d * (D d⁻¹ * M) = M
    rw [← Matrix.mul_assoc, D_mul, mul_inv_cancel₀ (ne_of_gt hd), D_one, one_mul]
  have P_det (t : unitInterval) : (P t).det ≠ 0 := by
    change (D (1 - (t : Real) + (t : Real) * d) * (p t).val).det ≠ 0
    rw [Matrix.det_mul, detD, (p t).property, mul_one]
    have ht0 : 0 ≤ (t : Real) := t.property.1
    have ht1 : (t : Real) ≤ 1 := t.property.2
    apply ne_of_gt
    by_cases ht : (t : Real) = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1)
        (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hd)
  have matrix_action (x : EuclideanSpace Real (Fin 3)) :
      M.mulVec (e x) = e (L x) := by
    exact LinearMap.toMatrix_mulVec_repr b b L.toLinearEquiv.toLinearMap x
  let H : ContinuousMap.Homotopy (ContinuousMap.id (EuclideanSpace Real (Fin 3)))
      (⟨L, L.continuous⟩ :
        C(EuclideanSpace Real (Fin 3), EuclideanSpace Real (Fin 3))) :=
    { toFun := fun z => e.symm ((P z.1).mulVec (e z.2))
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro x
        simp only [P_zero, Matrix.one_mulVec, ContinuousLinearEquiv.symm_apply_apply,
          ContinuousMap.id_apply]
      map_one_left := by
        intro x
        simp only [P_one, matrix_action, ContinuousLinearEquiv.symm_apply_apply,
          ContinuousMap.coe_mk] }
  refine ⟨H, ?_⟩
  intro t x hx hzero
  apply hx
  have hunit : IsUnit (P t) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (P_det t))
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hz : (P t).mulVec (e x) = 0 := by
    have hz := congrArg e hzero
    change e (e.symm ((P t).mulVec (e x))) = e 0 at hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using hz
  apply e.injective
  simpa only [map_zero] using hinj (hz.trans (Matrix.mulVec_zero _).symm)

end Poincare.Topology
