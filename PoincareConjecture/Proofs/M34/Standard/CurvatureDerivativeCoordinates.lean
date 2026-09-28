import PoincareConjecture.Proofs.M34.Standard.ConnectionDifferenceAlgebra
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy



noncomputable def rawComponent {n : ℕ} (l j k m : Fin n) : FS n →L[ℝ] ℝ where
  toFun R := raw R l j k m
  map_add' R S := by simp only [raw, map_add, add_apply]
  map_smul' r R := by simp only [raw, map_smul, smul_apply, RingHom.id_apply]
  cont := by unfold raw; fun_prop



theorem raw_eq_sum_coordinates {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (S : FS n) (l j k m : Fin n) :
    raw S l j k m = ∑ beta : Fin dS,
      raw (qS.symm (EuclideanSpace.single beta 1)) l j k m * qS S beta := by
  simpa only [rawComponent, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul, mul_comm] using
      (rawComponent l j k m).toLinearMap.apply_eq_sum_equiv_coordinates qS S



theorem fderiv_raw_eq_sum_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {S : E → FS n} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) (l j k m : Fin n) :
    fderiv ℝ (fun y => raw (S y) l j k m) x v =
      ∑ beta : Fin dS, raw (qS.symm (EuclideanSpace.single beta 1)) l j k m *
        fderiv ℝ (fun y => qS (S y) beta) x v := by
  have hleft := congrArg (fun L => L v)
    ((rawComponent l j k m).hasFDerivAt.comp x hS.hasFDerivAt).fderiv
  have hright (beta : Fin dS) :
      fderiv ℝ (fun y => qS (S y) beta) x v = qS (fderiv ℝ S x v) beta := by
    let L : FS n →L[ℝ] ℝ := (EuclideanSpace.proj beta).comp qS.toContinuousLinearMap
    exact congrArg (fun A => A v) (L.hasFDerivAt.comp x hS.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => raw (S y) l j k m) x v = raw (fderiv ℝ S x v) l j k m at hleft
  rw [hleft]
  simp_rw [hright]
  exact raw_eq_sum_coordinates qS _ l j k m



theorem sum_fderiv_raw_eq_ricciGradientCoordinates {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {S : V n → FS n} {x : V n}
    (hS : DifferentiableAt ℝ S x) (i j k : Fin n) :
    (∑ l : Fin n, fderiv ℝ (fun y => raw (S y) l l j k) x (EuclideanSpace.single i 1)) =
      ricciGradientCoordinates qS
        (fun beta => fderiv ℝ (fun y => qS (S y) beta.1) x
          (EuclideanSpace.single beta.2 1)) i j k := by
  simp_rw [fderiv_raw_eq_sum_coordinates qS hS]
  dsimp only [ricciGradientCoordinates, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

end PoincareConjecture.M34.DifferenceEnergy
