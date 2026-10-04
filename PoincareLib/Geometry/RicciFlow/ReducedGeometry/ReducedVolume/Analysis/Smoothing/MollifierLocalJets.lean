import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Analysis.Smoothing.MollifierJets
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Analysis.Smoothing.MollifierLocality
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Analysis.Smoothing.LocalSmoothExtension

/-!
# C2 convergence at every smooth germ

Compact smooth representatives agree with the original function near
the evaluation point. Small kernels see only that neighborhood, so the
global compact-data jet convergence applies to each original C2 germ.
-/

set_option autoImplicit false

open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology

namespace PoincareMT.ReducedVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Shrinking kernels converge in both scalar derivative jets at each C2 germ. -/
theorem normed_convolution_local_jets_tendsto {κ : ℕ → ContDiffBump (0 : E)}
    (hκ : Tendsto (fun j ↦ (κ j).rOut) atTop (𝓝 0)) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    Tendsto (fun j ↦ fderiv ℝ ((κ j).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      atTop (𝓝 (fderiv ℝ f x)) ∧
    Tendsto (fun j ↦ fderiv ℝ (fderiv ℝ ((κ j).normed μ ⋆[lsmul ℝ ℝ, μ] f)) x)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) x)) := by
  obtain ⟨g, hg, hgc, hfg⟩ := exists_compact_contDiff_two_of_germ hf
  have hj := normed_convolution_jets_tendsto (μ := μ) hκ hgc hg x
  have he := eventually_normed_convolution_eventuallyEq (μ := μ) hκ hfg
  rw [hfg.fderiv_eq, hfg.fderiv.fderiv_eq]
  constructor
  · apply hj.2.1.congr'
    exact he.mono (fun j hj ↦ hj.fderiv_eq.symm)
  · apply hj.2.2.congr'
    exact he.mono (fun j hj ↦ hj.fderiv.fderiv_eq.symm)

end PoincareMT.ReducedVolume
