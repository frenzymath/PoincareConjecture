import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Coordinates.MetricConvergence

/-!
# Partial pointed flow convergence on an included time window

The actual flow and every mixed within jet augment the spatial partial
limit on the same carrier. This fixed-window record retains time
endpoints and finite-radius source boundary control without asserting
completeness. It supports Morgan--Tian Definition 5.12 and Proposition
5.14, pp. 90-91; see task derivation 09.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

/-- Actual partial convergence on one included time window, extending
the spatial limit at the included base time. This is the fixed-window
form used for Morgan--Tian Definition 5.12, pp. 90-91 (derivation 09). -/
structure PartialPointedFlowConvergence {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} (F : ∀ k, RicciFlow n (M k) J)
    (p : ∀ k, M k) (A t₀ : ℝ) extends
      PartialPointedMetricConvergence (fun k => (F k).metric t₀) p A where
  /-- The spatial base time belongs to the specified flow interval. -/
  baseTime_mem : t₀ ∈ J
  /-- A genuine Ricci flow on the same partial limit carrier. -/
  limitFlow : @RicciFlow n limitCarrier.carrier limitCarrier.topologicalSpace
    limitCarrier.chartedSpace limitCarrier.isManifold J
  /-- Its base-time metric is the metric of the spatial partial limit. -/
  metric_at_baseTime : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    limitFlow.metric t₀ = limitMetric
  /-- Every actual mixed within jet converges in each chosen limit chart. -/
  spacetime_metric_jets : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    ∀ q m K, IsCompact K → K ⊆ J ×ˢ (extChartAt (𝓡 n) q).target →
      TendstoUniformlyOn
        (fun j => iteratedFDerivWithin ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((F (subsequence j)).metric z.1).pullbackCoefficients
              (embedding j ∘ (extChartAt (𝓡 n) q).symm) z.2)
          (J ×ˢ (extChartAt (𝓡 n) q).target))
        (iteratedFDerivWithin ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            (limitFlow.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2)
          (J ×ˢ (extChartAt (𝓡 n) q).target)) atTop K

/-- A partial flow limit of a strict subsequence is a limit of the
original source sequence, retaining all included-time jets
(Morgan--Tian Definition 5.12, pp. 90-91; derivation 09). -/
noncomputable def PartialPointedFlowConvergence.reindex
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} {F : ∀ k, RicciFlow n (M k) J}
    {p : ∀ k, M k} {A t₀ : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (G : PartialPointedFlowConvergence (fun k => F (φ k)) (fun k => p (φ k)) A t₀) :
    PartialPointedFlowConvergence F p A t₀ where
  toPartialPointedMetricConvergence := G.toPartialPointedMetricConvergence.reindex hφ
  baseTime_mem := G.baseTime_mem
  limitFlow := G.limitFlow
  metric_at_baseTime := G.metric_at_baseTime
  spacetime_metric_jets := G.spacetime_metric_jets

end PoincareMT.M28
