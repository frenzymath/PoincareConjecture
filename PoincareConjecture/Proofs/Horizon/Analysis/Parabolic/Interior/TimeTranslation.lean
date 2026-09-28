import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactSlices
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def timeTranslate (c : ℝ) (f : E × ℝ → F) (p : E × ℝ) : F :=
  f (p.1, p.2 + c)

theorem contDiff_timeTranslate (c : ℝ) {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (timeTranslate c f) :=
  hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem hasCompactSupport_timeTranslate (c : ℝ) {f : E × ℝ → F}
    (hf : HasCompactSupport f) : HasCompactSupport (timeTranslate c f) := by
  have h := hf.comp_isClosedEmbedding (Homeomorph.addRight ((0 : E), c)).isClosedEmbedding
  convert h using 1
  funext p
  change f (p.1, p.2 + c) = f (p.1 + 0, p.2 + c)
  rw [add_zero]

theorem timeDerivative_timeTranslate (c : ℝ) {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (p : E × ℝ) :
    timeDerivative (timeTranslate c f) p = timeDerivative f (p.1, p.2 + c) := by
  have h := (hasDerivAt_timeSlice (hf.differentiable (by simp)) p.1 (p.2 + c)).scomp p.2
    ((hasDerivAt_id p.2).add_const c)
  have h' := hasDerivAt_timeSlice ((contDiff_timeTranslate c hf).differentiable (by simp))
    p.1 p.2
  exact h'.unique (by simpa [timeTranslate, Function.comp_def] using h)

theorem spatialDerivative_timeTranslate (c : ℝ) {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (p : E × ℝ) :
    spatialDerivative (timeTranslate c f) p = spatialDerivative f (p.1, p.2 + c) := by
  rw [← fderiv_spatialSlice (contDiff_timeTranslate c hf) p.1 p.2,
    ← fderiv_spatialSlice hf p.1 (p.2 + c)]
  rfl

theorem spatialDerivative_spatialDerivative_timeTranslate (c : ℝ)
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (p : E × ℝ) :
    spatialDerivative (spatialDerivative (timeTranslate c f)) p =
      spatialDerivative (spatialDerivative f) (p.1, p.2 + c) := by
  have h : spatialDerivative (timeTranslate c f) = timeTranslate c (spatialDerivative f) :=
    funext (spatialDerivative_timeTranslate c hf)
  rw [h, spatialDerivative_timeTranslate c (contDiff_spatialDerivative hf)]

theorem fderiv_fderiv_timeTranslate_slice (c : ℝ) (f : E × ℝ → F) (x : E) (t : ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => timeTranslate c f (z, t)) y) x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t + c)) y) x := rfl

end Poincare.Parabolic.Interior
