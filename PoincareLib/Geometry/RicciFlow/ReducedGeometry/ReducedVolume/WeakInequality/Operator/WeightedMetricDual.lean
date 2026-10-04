import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Metric.Hessian.MetricDualDerivative
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Analysis.Integration.SupportedCalculus

/-!
# Density-weighted metric duals with local support

The field used in chart divergence is explicit in the bilinear metric,
its scalar volume density and the scalar differential. A compactly
supported scalar test gives a compactly supported globally C1 field
even when the metric is smooth only on the containing chart.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareMT.ReducedVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual density times the metric dual of a scalar differential in coordinates. -/
noncomputable def weightedMetricDual (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (ρ f : E → ℝ) (x : E) : E :=
  ρ x • (B x).inverse (fderiv ℝ f x)

/-- Local C1 metric and density data and a C2 scalar give a C1 weighted dual. -/
theorem weightedMetricDual_contDiffAt
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ f : E → ℝ} {x : E}
    (hB : ContDiffAt ℝ 1 B x) (hρ : ContDiffAt ℝ 1 ρ x)
    (hf : ContDiffAt ℝ 2 f x) (hi : (B x).IsInvertible) :
    ContDiffAt ℝ 1 (weightedMetricDual B ρ f) x :=
  hρ.smul (metricDual_contDiffAt hB hf hi)

omit [CompleteSpace E] in
/-- The weighted dual is supported in the closed support of the scalar. -/
theorem tsupport_weightedMetricDual_subset
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (ρ f : E → ℝ) :
    tsupport (weightedMetricDual B ρ f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hnot
  apply hx
  simp only [weightedMetricDual, fderiv_of_notMem_tsupport ℝ hnot, map_zero, smul_zero]

/-- A supported C2 scalar test has a globally C1 weighted metric dual. -/
theorem weightedMetricDual_contDiff_of_tsupport_subset
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hρ : ContDiffOn ℝ 1 ρ U)
    (hf : ContDiffOn ℝ 2 f U) (hi : ∀ x ∈ U, (B x).IsInvertible)
    (hs : tsupport f ⊆ U) :
    ContDiff ℝ 1 (weightedMetricDual B ρ f) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset hU _
    ((tsupport_weightedMetricDual_subset B ρ f).trans hs)
  intro x hx
  exact (weightedMetricDual_contDiffAt (hB.contDiffAt (hU.mem_nhds hx))
    (hρ.contDiffAt (hU.mem_nhds hx)) (hf.contDiffAt (hU.mem_nhds hx))
    (hi x hx)).contDiffWithinAt

omit [CompleteSpace E] in
/-- Compact support is preserved by the weighted metric dual. -/
theorem weightedMetricDual_hasCompactSupport
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (ρ : E → ℝ) {f : E → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (weightedMetricDual B ρ f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_weightedMetricDual_subset B ρ f)

end PoincareMT.ReducedVolume
