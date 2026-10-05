import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Exponential.ModelExponential

/-!
# The inverse and exact balls of the fixed-frame model

The standard pole expressed in the limiting orthonormal frame maps
Euclidean balls to standard metric balls of the same radius.
Morgan--Tian, Claim 16.6 and Corollary 16.7, pp. 371-372; see
`derivations/20-exponential-model-and-convergence.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

local notation "E" => StandardCapSpace

/-- The actual inverse of the fixed-frame standard exponential.
Source: the exponential adjustment in Claim 16.6, pp. 371-372. -/
noncomputable def standardFrameLogarithm (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    E → E := L.symm ∘ standardRadialLogarithm g₀

/-- The fixed model inverse is smooth on the entire standard cap.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFrameLogarithm_contDiff (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    ContDiff ℝ ∞ (standardFrameLogarithm g₀ L) :=
  L.symm.contDiff.comp (standardRadialLogarithm_contDiff g₀)

/-- The fixed-frame logarithm is a left inverse of its exponential.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFrameLogarithm_exponential
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (v : E) :
    standardFrameLogarithm g₀ L (standardFrameExponential g₀ L v) = v := by
  simp only [standardFrameLogarithm, standardFrameExponential, Function.comp_apply,
    standardRadialLogarithm_exponential, ContinuousLinearEquiv.symm_apply_apply]

/-- The fixed-frame logarithm is also a right inverse.
Source: Claim 16.6, pp. 371-372. -/
theorem standardFrameExponential_logarithm
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (v : E) :
    standardFrameExponential g₀ L (standardFrameLogarithm g₀ L v) = v := by
  simp only [standardFrameLogarithm, standardFrameExponential, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, standardRadialExponential_logarithm]

/-- Orthonormality identifies the model tangent norm with the Euclidean
norm in the fixed frame. Source: Corollary 16.7, p. 372. -/
theorem standard_frame_tangentNorm (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (hL : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w) (v : E) :
    g₀.metric.tangentNorm 0 (L v) = ‖v‖ := by
  rw [RiemannianMetric.tangentNorm, hL, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg v)]

/-- The fixed-frame model maps every positive Euclidean ball exactly
onto the standard metric ball of the same radius.
Source: the exact-ball adjustment in Claim 16.6, pp. 371-372. -/
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

/-- The model inverse takes every standard ball to the literal
Euclidean parameter ball. Source: Claim 16.6, pp. 371-372. -/
theorem standardFrameLogarithm_image_ball
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (hL : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {r : ℝ} (hr : 0 < r) :
    standardFrameLogarithm g₀ L '' g₀.metric.ball 0 r = Metric.ball 0 r := by
  rw [← standardFrameExponential_image_ball g₀ L hL hr, image_image]
  simp only [standardFrameLogarithm_exponential, image_id']

end PoincareMT.M44
