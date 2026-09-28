
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Topology
open Filter

namespace Poincare.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma hasDerivAt_fderiv_time_of_eventually
    {f : ℝ × E → F} {df : E → F} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (t, x))
    (hdf : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => f (s, y)) (df y) t) (v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => f (s, y)) x v)
      (fderiv ℝ df x v) t := by
  have hd := (hf.fderiv_right (m := 1)
    (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hn : ∀ᶠ p in 𝓝 (t, x), DifferentiableAt ℝ f p :=
    ((hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually
      (by decide)).mono
      fun p hp => hp.differentiableAt one_ne_zero
  have hs := hd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hl := hs.clm_apply (hasDerivAt_const t (0, v))
  simp only [ContinuousLinearMap.map_zero, add_zero] at hl
  have he : (fun s => fderiv ℝ (fun y => f (s, y)) x v) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (s, x) (0, v)) := by
    have ht : Tendsto (fun s : ℝ => (s, x)) (𝓝 t) (𝓝 (t, x)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually hn] with s hs
    have h := hs.hasFDerivAt.comp x
      ((hasFDerivAt_const (c := s) x).prodMk (hasFDerivAt_id x))
    simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] F => A v) h.fderiv
  have hspace := hd.hasFDerivAt.comp x
    ((hasFDerivAt_const (c := t) x).prodMk (hasFDerivAt_id x))
  have hr := hspace.clm_apply (hasFDerivAt_const (c := (1, (0 : E))) x)
  have he' : df =ᶠ[𝓝 x] (fun y => fderiv ℝ f (t, y) (1, 0)) := by
    have hx : Tendsto (fun y : E => (t, y)) (𝓝 x) (𝓝 (t, x)) :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hx.eventually hn, hdf] with y hy hdy
    have h := hy.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact hdy.unique h
  have hr' := congrArg (fun A : E →L[ℝ] F => A v)
    (hr.congr_of_eventuallyEq he').fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.map_zero, zero_add,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] at hr'
  have hsym := hf.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    (1, 0) (0, v)
  apply (hl.congr_of_eventuallyEq he).congr_deriv
  simpa only [Function.comp_def] using hsym.trans hr'.symm



lemma hasDerivAt_fderiv_time
    {f : ℝ × E → ℝ} {df : E → ℝ} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (t, x))
    (hdf : ∀ y, HasDerivAt (fun s => f (s, y)) (df y) t) (v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => f (s, y)) x v)
      (fderiv ℝ df x v) t :=
  hasDerivAt_fderiv_time_of_eventually hf (Filter.Eventually.of_forall hdf) v

end Poincare.Analysis
