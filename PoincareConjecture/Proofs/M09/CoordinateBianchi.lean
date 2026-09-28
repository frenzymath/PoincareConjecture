import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coefficientCurvature (C : E → E →L[ℝ] E →L[ℝ] E)
    (x u v w : E) : E :=
  fderiv ℝ C x u v w - fderiv ℝ C x v u w +
    C x u (C x v w) - C x v (C x u w)

theorem coefficientCurvature_antisymm (C : E → E →L[ℝ] E →L[ℝ] E)
    (x u v w : E) : coefficientCurvature C x u v w = -coefficientCurvature C x v u w := by
  unfold coefficientCurvature
  abel

private theorem hasFDerivAt_eval_const
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → V →L[ℝ] W} {f' : E →L[ℝ] V →L[ℝ] W} {x : E}
    (hf : HasFDerivAt f f' x) (v : V) :
    HasFDerivAt (fun y ↦ f y v) (f'.flip v) x := by
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using
    hf.clm_apply (hasFDerivAt_const v x)

set_option maxHeartbeats 800000 in

theorem fderiv_coefficientCurvature (C : E → E →L[ℝ] E →L[ℝ] E)
    (x : E) (hC : DifferentiableAt ℝ C x)
    (hDC : DifferentiableAt ℝ (fderiv ℝ C) x) (a u v w : E) :
    fderiv ℝ (fun y ↦ coefficientCurvature C y u v w) x a =
      fderiv ℝ (fderiv ℝ C) x a u v w -
        fderiv ℝ (fderiv ℝ C) x a v u w +
        (fderiv ℝ C x a u (C x v w) + C x u (fderiv ℝ C x a v w)) -
        (fderiv ℝ C x a v (C x u w) + C x v (fderiv ℝ C x a u w)) := by
  have hfirst := hasFDerivAt_eval_const
    (hasFDerivAt_eval_const (hasFDerivAt_eval_const hDC.hasFDerivAt u) v) w
  have hsecond := hasFDerivAt_eval_const
    (hasFDerivAt_eval_const (hasFDerivAt_eval_const hDC.hasFDerivAt v) u) w
  have hCu := hasFDerivAt_eval_const hC.hasFDerivAt u
  have hCv := hasFDerivAt_eval_const hC.hasFDerivAt v
  have hleft := hCu.clm_apply (hasFDerivAt_eval_const hCv w)
  have hright := hCv.clm_apply (hasFDerivAt_eval_const hCu w)
  have h := congrArg (fun L : E →L[ℝ] E ↦ L a)
    (((hfirst.sub hsecond).add hleft).sub hright).fderiv
  change fderiv ℝ (fun y ↦ coefficientCurvature C y u v w) x a = _ at h
  simpa only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, add_zero, zero_add, add_comm] using h

noncomputable def coefficientCurvatureExteriorDerivative
    (C : E → E →L[ℝ] E →L[ℝ] E) (x a u v w : E) : E :=
  fderiv ℝ (fun y ↦ coefficientCurvature C y u v w) x a +
    C x a (coefficientCurvature C x u v w) -
    coefficientCurvature C x u v (C x a w)

set_option maxHeartbeats 800000 in
theorem coefficientCurvature_exterior_bianchi (C : E → E →L[ℝ] E →L[ℝ] E)
    (x : E) (hC : ContDiffAt ℝ ∞ C x) (a u v w : E) :
    coefficientCurvatureExteriorDerivative C x a u v w +
      coefficientCurvatureExteriorDerivative C x u v a w +
      coefficientCurvatureExteriorDerivative C x v a u w = 0 := by
  have hD := hC.differentiableAt (by simp)
  have hDD := (hC.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hsym := hC.isSymmSndFDerivAt htwo
  unfold coefficientCurvatureExteriorDerivative
  rw [fderiv_coefficientCurvature C x hD hDD,
    fderiv_coefficientCurvature C x hD hDD,
    fderiv_coefficientCurvature C x hD hDD]
  simp only [coefficientCurvature, map_add, map_sub]
  rw [hsym a u, hsym a v, hsym u v]
  abel

noncomputable def coefficientCurvatureCovariantDerivative
    (C : E → E →L[ℝ] E →L[ℝ] E) (x a u v w : E) : E :=
  coefficientCurvatureExteriorDerivative C x a u v w -
    coefficientCurvature C x (C x a u) v w -
    coefficientCurvature C x u (C x a v) w

theorem coefficientCurvature_bianchi (C : E → E →L[ℝ] E →L[ℝ] E)
    (x : E) (hC : ContDiffAt ℝ ∞ C x)
    (hsym : ∀ u v, C x u v = C x v u) (a u v w : E) :
    coefficientCurvatureCovariantDerivative C x a u v w +
      coefficientCurvatureCovariantDerivative C x u v a w +
      coefficientCurvatureCovariantDerivative C x v a u w = 0 := by
  have hb := coefficientCurvature_exterior_bianchi C x hC a u v w
  unfold coefficientCurvatureCovariantDerivative
  rw [hsym u a, hsym v a, hsym v u,
    coefficientCurvature_antisymm C x u (C x a v) w,
    coefficientCurvature_antisymm C x v (C x a u) w,
    coefficientCurvature_antisymm C x a (C x u v) w]
  calc
    _ = coefficientCurvatureExteriorDerivative C x a u v w +
        coefficientCurvatureExteriorDerivative C x u v a w +
        coefficientCurvatureExteriorDerivative C x v a u w := by abel
    _ = 0 := hb

end PoincareConjecture.Proofs.M09
