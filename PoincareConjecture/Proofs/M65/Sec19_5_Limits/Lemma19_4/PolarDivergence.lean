import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul











set_option autoImplicit false

open Set MeasureTheory Real
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



noncomputable def m65PolarRadialFlux (X : LoopPlane → LoopPlane)
    (r t : ℝ) : ℝ :=
  r * inner ℝ (X (r • Proofs.M58.angularPoint t)) (Proofs.M58.angularPoint t)



noncomputable def m65PolarAngularFlux (X : LoopPlane → LoopPlane)
    (r t : ℝ) : ℝ :=
  inner ℝ (X (r • Proofs.M58.angularPoint t)) (Proofs.M58.angularVector t)



theorem m65AngularVector_hasDerivAt (t : ℝ) :
    HasDerivAt Proofs.M58.angularVector (-Proofs.M58.angularPoint t) t := by
  have h : HasDerivAt (fun s : ℝ => ![-sin s, cos s]) ![-cos t, -sin t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hasDerivAt_sin t).neg
    · exact hasDerivAt_cos t
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
  convert! L.hasFDerivAt.comp_hasDerivAt t h using 1
  ext i
  fin_cases i <;> rfl




theorem m65PolarDivergencePointwise
    (X : LoopPlane → LoopPlane) {r t : ℝ}
    (hX : ContDiffAt ℝ 1 X (r • Proofs.M58.angularPoint t)) :
    deriv (fun s : ℝ => m65PolarRadialFlux X s t) r +
        deriv (fun θ : ℝ => m65PolarAngularFlux X r θ) t =
      r * (inner ℝ
        ((fderiv ℝ X (r • Proofs.M58.angularPoint t))
          (Proofs.M58.angularPoint t)) (Proofs.M58.angularPoint t) +
        inner ℝ
          ((fderiv ℝ X (r • Proofs.M58.angularPoint t))
            (Proofs.M58.angularVector t)) (Proofs.M58.angularVector t)) := by
  let e : LoopPlane := Proofs.M58.angularPoint t
  let τ : LoopPlane := Proofs.M58.angularVector t
  let p : LoopPlane := r • e
  have he : HasDerivAt (fun s : ℝ => s • e) e r := by
    simpa +instances only [one_smul] using! (hasDerivAt_id r).smul_const e
  have hθ : HasDerivAt (fun s : ℝ => r • Proofs.M58.angularPoint s)
      (r • τ) t :=
    (Proofs.M58.hasDerivAt_angularPoint t).const_smul r
  have hXp : HasFDerivAt X (fderiv ℝ X p) p :=
    (hX.differentiableAt (by simp)).hasFDerivAt
  have hXr : HasDerivAt (fun s : ℝ => X (s • e))
      ((fderiv ℝ X p) e) r := by
    simpa +instances only [p, Function.comp_def] using! hXp.comp_hasDerivAt r he
  have hXt : HasDerivAt (fun s : ℝ => X (r • Proofs.M58.angularPoint s))
      ((fderiv ℝ X p) (r • τ)) t := by
    simpa +instances only [p, Function.comp_def] using! hXp.comp_hasDerivAt t hθ
  have hrad : HasDerivAt
      (fun s : ℝ => m65PolarRadialFlux X s t)
      (inner ℝ (X p) e + r * inner ℝ ((fderiv ℝ X p) e) e) r := by
    simpa +instances only [m65PolarRadialFlux, e, p, inner_zero_right, zero_add, one_mul,
      id_eq, Pi.mul_apply] using!
      (hasDerivAt_id r).mul (hXr.inner ℝ (hasDerivAt_const r e))
  have hang : HasDerivAt
      (fun s : ℝ => m65PolarAngularFlux X r s)
      (inner ℝ ((fderiv ℝ X p) (r • τ)) τ +
        inner ℝ (X p) (-e)) t := by
    simpa only [m65PolarAngularFlux, τ, e, p, add_comm] using
      hXt.inner ℝ (m65AngularVector_hasDerivAt t)
  rw [hrad.deriv, hang.deriv]
  simp only [map_smul, real_inner_smul_left, inner_neg_right]
  change inner ℝ (X p) e + r * inner ℝ ((fderiv ℝ X p) e) e +
      (r * inner ℝ ((fderiv ℝ X p) τ) τ - inner ℝ (X p) e) = _
  ring



theorem m65PolarTrace_eq (A : LoopPlane →L[ℝ] LoopPlane) (t : ℝ) :
    inner ℝ (A (Proofs.M58.angularPoint t)) (Proofs.M58.angularPoint t) +
      inner ℝ (A (Proofs.M58.angularVector t)) (Proofs.M58.angularVector t) =
        ∑ i : Fin 2, inner ℝ (A (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  let b : Fin 2 → LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ
  have he : Proofs.M58.angularPoint t = cos t • b 0 + sin t • b 1 := by
    ext i
    fin_cases i <;> simp [b, Proofs.M58.angularPoint, EuclideanSpace.single]
  have hτ : Proofs.M58.angularVector t = (-sin t) • b 0 + cos t • b 1 := by
    ext i
    fin_cases i <;> simp [b, Proofs.M58.angularVector, EuclideanSpace.single]
  rw [he, hτ]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, Fin.sum_univ_two]
  change _ = inner ℝ (A (b 0)) (b 0) + inner ℝ (A (b 1)) (b 1)
  calc
    _ = (cos t ^ 2 + sin t ^ 2) *
        (inner ℝ (A (b 0)) (b 0) + inner ℝ (A (b 1)) (b 1)) := by ring
    _ = _ := by rw [cos_sq_add_sin_sq, one_mul]

end PoincareConjecture
