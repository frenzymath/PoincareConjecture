import PoincareConjecture.Proofs.M10.ProductDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Slope









set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]


theorem tendsto_scaled_horizontal_fderiv {P : X × ℝ → Y} {x : X} {c : Y}
    (L : X →L[ℝ] Y) (hP : ContDiffAt ℝ 2 P (x, 0))
    (hzero : ∀ v : X, P (v, 0) = c)
    (htime : ∀ v : X, fderiv ℝ P (v, 0) (0, 1) = L v) (h : X) :
    Tendsto (fun s : ℝ ↦ s⁻¹ • fderiv ℝ P (x, s) (h, 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (L h)) := by
  let z : X × ℝ := (x, 0)
  let et : X × ℝ := (0, 1)
  let eh : X × ℝ := (h, 0)
  have hDP : DifferentiableAt ℝ (fderiv ℝ P) z :=
    (hP.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hEval (w : X × ℝ) : HasFDerivAt (fun z ↦ fderiv ℝ P z w)
      ((fderiv ℝ (fderiv ℝ P) z).flip w) z := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hDP.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  have hV := (hEval et).comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (0 : ℝ))
  have hVL : HasFDerivAt (fun v : X ↦ fderiv ℝ P (v, 0) et) L x :=
    L.hasFDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall htime)
  have hsecond := congrArg (fun D : X →L[ℝ] Y ↦ D h) (hV.unique hVL)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inl_apply] at hsecond
  have hA := (hEval eh).comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
  have hsymm := (hP.isSymmSndFDerivAt (by simp)).eq et eh
  have hA' : HasDerivAt (fun s : ℝ ↦ fderiv ℝ P (x, s) (h, 0)) (L h) 0 := by
    apply hA.congr_deriv
    exact hsymm.trans hsecond
  have hA0 : fderiv ℝ P (x, 0) (h, 0) = 0 := by
    rw [fderiv_horizontal_eq (hP.differentiableAt two_ne_zero) h]
    simp only [show (fun v : X ↦ P (v, 0)) = (fun _ ↦ c) from funext hzero,
      fderiv_const_apply, zero_apply]
  simpa only [zero_add, hA0, sub_zero] using hA'.tendsto_slope_zero_right

end PoincareConjecture.M10
