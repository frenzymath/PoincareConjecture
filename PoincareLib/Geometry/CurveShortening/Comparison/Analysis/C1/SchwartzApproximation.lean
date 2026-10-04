import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Local.Approximation
import PoincareLib.Geometry.Riemannian.LoopSpace.Width
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Schwartz approximation of a C1 test and its actual derivative

A cutoff retains the test near the compact set. A single normalized
convolution approximates both its values and its derivative, and a final
cutoff gives a Schwartz function with the same approximation there.
Source: M40 normalized smoothing; M60 C1 smoothing for MT Lemma 18.10;
M64 boundary semicircle assembly derivation.

Context: Morgan--Tian Lemma 19.15, printed pp. 447-449; this analytic helper supports
the actual annular minimizer and boundary regularity construction.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ContDiff SchwartzMap Convolution

namespace PoincareMT

/-- Every C1 scalar test has a Schwartz approximation of its full first jet on a prescribed
compact set. Source: derivations/2026-09-26-boundary-semicircle-assembly.md, C1 Green tests. -/
theorem m64C1_schwartz_approximation {K : Set LoopPlane} (hK : IsCompact K)
    {f : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : 𝓢(LoopPlane, ℝ), ∀ x ∈ K,
      dist (g x) (f x) < epsilon ∧ dist (fderiv ℝ g x) (fderiv ℝ f x) < epsilon := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : LoopPlane)
  let chi : ContDiffBump (0 : LoopPlane) := ⟨R, R + 1, hR, by linarith⟩
  let F := fun x => chi x * f x
  have hF : ContDiff ℝ 1 F := chi.contDiff.mul hf
  have hFc : HasCompactSupport F := chi.hasCompactSupport.mul_right
  have hnear (x : LoopPlane) (hx : x ∈ K) : F =ᶠ[𝓝 x] f := by
    filter_upwards [chi.eventuallyEq_one_of_mem_ball (hKR hx)] with y hy
    simp only [F, hy, Pi.one_apply, one_mul]
  obtain ⟨r0, hr0, h0⟩ := M40.exists_radius_normalizedConvolution_dist_lt_uniform
    (μ := volume) (hFc.uniformContinuous_of_continuous hF.continuous) hepsilon
  obtain ⟨r1, hr1, h1⟩ := M40.exists_radius_normalizedConvolution_dist_lt_uniform
    (μ := volume) ((hFc.fderiv ℝ).uniformContinuous_of_continuous
      (hF.continuous_fderiv one_ne_zero)) hepsilon
  let r := min r0 r1 / 2
  have hr : 0 < r := half_pos (lt_min hr0 hr1)
  let phi : ContDiffBump (0 : LoopPlane) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let G := M40.normalizedConvolution volume phi F
  have hG : ContDiff ℝ ∞ G :=
    M40.normalizedConvolution_contDiff phi hF.continuous.locallyIntegrable
  have hDG (x : LoopPlane) : fderiv ℝ G x =
      M40.normalizedConvolution volume phi (fderiv ℝ F) x :=
    (hFc.hasFDerivAt_convolution_right (μ := volume) (lsmul ℝ ℝ)
      ((phi.continuous_normed (μ := volume)).locallyIntegrable) hF x).fderiv
  let g : 𝓢(LoopPlane, ℝ) := chi.hasCompactSupport.mul_right.toSchwartzMap
    (chi.contDiff.mul hG)
  refine ⟨g, ?_⟩
  intro x hx
  have hgnear : (g : LoopPlane → ℝ) =ᶠ[𝓝 x] G := by
    filter_upwards [chi.eventuallyEq_one_of_mem_ball (hKR hx)] with y hy
    change chi y * G y = G y
    rw [hy, Pi.one_apply, one_mul]
  rw [hgnear.self_of_nhds, hgnear.fderiv_eq, ← (hnear x hx).self_of_nhds,
    ← (hnear x hx).fderiv_eq, hDG]
  exact ⟨h0 phi ((half_lt_self (lt_min hr0 hr1)).le.trans (min_le_left _ _)) x,
    h1 phi ((half_lt_self (lt_min hr0 hr1)).le.trans (min_le_right _ _)) x⟩

end PoincareMT
