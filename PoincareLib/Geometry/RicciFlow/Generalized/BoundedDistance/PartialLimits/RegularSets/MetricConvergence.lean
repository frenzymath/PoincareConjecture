import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.Regularity
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.FlowCarrier

/-!
# Pointed metric convergence with regular-component capture

The spatial output for the total-volume specialization of Morgan--Tian
Theorem 5.6, printed pp. 85-87, retains the actual smooth metric, compact
exhaustion, pointed source maps and all metric jets. Every fixed regular
base component is eventually covered by one fixed compact stage. There is
no radial frontier, global properness or completeness field.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

/-- The actual nonradial spatial conclusion of Theorem 5.6 for regular
base components, with arbitrary source universe and a countable limit. -/
structure RegularPointedMetricConvergence {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (p : ∀ k, M k) where
  /-- The countable smooth quotient. -/
  limitCarrier : FlowCarrier.{0} n
  /-- The glued positive smooth metric. -/
  limitMetric : limitCarrier.metric
  /-- The limit of the retained source basepoints. -/
  base : limitCarrier.carrier
  /-- A single strict selection for all charts and derivatives. -/
  subsequence : ℕ → ℕ
  /-- Strictness preserves every earlier source tail. -/
  subsequence_strictMono : StrictMono subsequence
  /-- The actual open domains of the source embeddings. -/
  exhaustion : ℕ → Set limitCarrier.carrier
  /-- Each stage is open. -/
  exhaustion_open : letI := limitCarrier.topologicalSpace
    ∀ j, IsOpen (exhaustion j)
  /-- Each stage is connected. -/
  exhaustion_connected : letI := limitCarrier.topologicalSpace
    ∀ j, IsConnected (exhaustion j)
  /-- Each stage contains the distinguished point. -/
  base_in_exhaustion : ∀ j, base ∈ exhaustion j
  /-- The closures of the stages are compact. -/
  exhaustion_compactClosure : letI := limitCarrier.topologicalSpace
    ∀ j, IsCompact (closure (exhaustion j))
  /-- The next stage contains the preceding closure. -/
  exhaustion_step : letI := limitCarrier.topologicalSpace
    ∀ j, closure (exhaustion j) ⊆ exhaustion (j + 1)
  /-- The stages exhaust the limit carrier. -/
  exhaustion_covers : (⋃ j, exhaustion j) = univ
  /-- Total extensions, used geometrically only on their stated domains. -/
  embedding : ∀ j, limitCarrier.carrier → M (subsequence j)
  /-- Each restricted source map is an open embedding. -/
  embedding_open : letI := limitCarrier.topologicalSpace
    ∀ j, Topology.IsOpenEmbedding (fun x : exhaustion j => embedding j x)
  /-- Each source map is a smooth local diffeomorphism on its domain. -/
  embedding_smooth : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    ∀ j, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (embedding j) (exhaustion j)
  /-- The actual retained basepoints are preserved. -/
  base_preserving : ∀ j, embedding j base = p (subsequence j)
  /-- All ordinary jets of actual pulled-back metric coefficients converge. -/
  metric_jets : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    ∀ q m K, IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ m ((g (subsequence j)).pullbackCoefficients
          (embedding j ∘ (extChartAt (𝓡 n) q).symm)))
        (iteratedFDeriv ℝ m (limitMetric.pullbackCoefficients
          (extChartAt (𝓡 n) q).symm)) atTop K
  /-- The stage is chosen before the source index and every point of the
  literal Definition 5.1 regular base component. -/
  regular_component_coverage : ∀ δ : ℝ, 0 < δ → ∃ j : ℕ, ∀ᶠ k in atTop,
    j ≤ k ∧ regularComponent (g (subsequence k)) (p (subsequence k)) δ ⊆
      embedding k '' exhaustion j

/-- A strict earlier extraction is retained literally in the final
source index. Theorem 5.6, printed pp. 86-87. -/
noncomputable def RegularPointedMetricConvergence.reindex
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (G : RegularPointedMetricConvergence (fun k => g (φ k)) (fun k => p (φ k))) :
    RegularPointedMetricConvergence g p where
  limitCarrier := G.limitCarrier
  limitMetric := G.limitMetric
  base := G.base
  subsequence := φ ∘ G.subsequence
  subsequence_strictMono := hφ.comp G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  base_in_exhaustion := G.base_in_exhaustion
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_step := G.exhaustion_step
  exhaustion_covers := G.exhaustion_covers
  embedding := G.embedding
  embedding_open := G.embedding_open
  embedding_smooth := G.embedding_smooth
  base_preserving := G.base_preserving
  metric_jets := G.metric_jets
  regular_component_coverage := G.regular_component_coverage

end PoincareMT.M28
