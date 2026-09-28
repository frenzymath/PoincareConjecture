import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ModelExponential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

noncomputable def standardFrameLogarithm (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    E → E := L.symm ∘ standardRadialLogarithm g₀

theorem standardFrameLogarithm_contDiff (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    ContDiff ℝ ∞ (standardFrameLogarithm g₀ L) :=
  L.symm.contDiff.comp (standardRadialLogarithm_contDiff g₀)

theorem standardFrameLogarithm_exponential
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (v : E) :
    standardFrameLogarithm g₀ L (standardFrameExponential g₀ L v) = v := by
  simp only [standardFrameLogarithm, standardFrameExponential, Function.comp_apply,
    standardRadialLogarithm_exponential, ContinuousLinearEquiv.symm_apply_apply]

theorem standardFrameExponential_logarithm
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (v : E) :
    standardFrameExponential g₀ L (standardFrameLogarithm g₀ L v) = v := by
  simp only [standardFrameLogarithm, standardFrameExponential, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, standardRadialExponential_logarithm]

theorem standard_frame_tangentNorm (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (hL : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w) (v : E) :
    g₀.metric.tangentNorm 0 (L v) = ‖v‖ := by
  rw [RiemannianMetric.tangentNorm, hL, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg v)]

theorem standardFrameExponential_image_ball
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (hL : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {r : ℝ} (hr : 0 < r) :
    standardFrameExponential g₀ L '' Metric.ball 0 r = g₀.metric.ball 0 r := by
  have hframe : L '' Metric.ball 0 r = {v | g₀.metric.tangentNorm 0 v < r} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change g₀.metric.tangentNorm 0 (L v) < r
      rw [standard_frame_tangentNorm g₀ L hL]
      simpa only [Metric.mem_ball, dist_zero_right] using hv
    · intro hw
      refine ⟨L.symm w, ?_, L.apply_symm_apply w⟩
      rw [Metric.mem_ball, dist_zero_right, ← standard_frame_tangentNorm g₀ L hL,
        L.apply_symm_apply]
      exact hw
  calc
    standardFrameExponential g₀ L '' Metric.ball 0 r =
        standardRadialExponential g₀ '' (L '' Metric.ball 0 r) :=
      (image_image (standardRadialExponential g₀) L (Metric.ball 0 r)).symm
    _ = g₀.metric.ball 0 r := by
      rw [hframe]
      exact standardRadialExponential_image_tangent_ball g₀ hr

theorem standardFrameLogarithm_image_ball
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (hL : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {r : ℝ} (hr : 0 < r) :
    standardFrameLogarithm g₀ L '' g₀.metric.ball 0 r = Metric.ball 0 r := by
  rw [← standardFrameExponential_image_ball g₀ L hL hr, image_image]
  simp only [standardFrameLogarithm_exponential, image_id']

end PoincareConjecture.M44
