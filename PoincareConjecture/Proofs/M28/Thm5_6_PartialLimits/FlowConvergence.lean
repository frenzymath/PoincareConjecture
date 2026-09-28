import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.MetricConvergence

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

structure PartialPointedFlowConvergence {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} (F : ∀ k, RicciFlow n (M k) J)
    (p : ∀ k, M k) (A t₀ : ℝ) extends
      PartialPointedMetricConvergence (fun k => (F k).metric t₀) p A where

  baseTime_mem : t₀ ∈ J

  limitFlow : @RicciFlow n limitCarrier.carrier limitCarrier.topologicalSpace
    limitCarrier.chartedSpace limitCarrier.isManifold J

  metric_at_baseTime : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    limitFlow.metric t₀ = limitMetric

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

end PoincareConjecture.M28
