import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients

/-!
# Partial pointed spatial metric convergence

Morgan--Tian Theorem 5.6, printed pp. 85-87, supplies spatial convergence
and source-boundary control below a finite radius. This local interface
mirrors `M28/Thm5_6_PartialLimits/MetricConvergence.lean` at commit
`dd738375b107926c5dfbdd1f2eed70f6c4f0c86f`, with identical fields and universe
choices. Its main-only imports do not provide a compactness theorem.

See `proof-work/tasks/M30/derivations/m28-partial-window-service.md` for the
source comparison and the later fieldwise replacement after lower promotion.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M30

/-- Actual spatial convergence with boundary control below `A`, for
Morgan--Tian Theorem 5.6, printed pp. 85-87. The fields match the pinned M28
partial metric convergence interface, including its `Type 0` limit carrier. -/
structure PartialPointedMetricConvergence {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (p : ∀ k, M k) (A : ℝ) where
  /-- The actual countable smooth limit carrier. -/
  limitCarrier : FlowCarrier.{0} n
  /-- The actual positive smooth limit metric. -/
  limitMetric : limitCarrier.metric
  /-- The pointed limit. -/
  base : limitCarrier.carrier
  /-- The retained source indices. -/
  subsequence : ℕ → ℕ
  /-- Extraction uses a strict subsequence. -/
  subsequence_strictMono : StrictMono subsequence
  /-- The compact-stage domains of the source embeddings. -/
  exhaustion : ℕ → Set limitCarrier.carrier
  /-- Each domain is open in the actual limit topology. -/
  exhaustion_open : letI := limitCarrier.topologicalSpace
    ∀ j, IsOpen (exhaustion j)
  /-- Each domain is connected. -/
  exhaustion_connected : letI := limitCarrier.topologicalSpace
    ∀ j, IsConnected (exhaustion j)
  /-- Every stage contains the basepoint. -/
  base_in_exhaustion : ∀ j, base ∈ exhaustion j
  /-- The closures are compact. -/
  exhaustion_compactClosure : letI := limitCarrier.topologicalSpace
    ∀ j, IsCompact (closure (exhaustion j))
  /-- A stage closure lies in the next domain. -/
  exhaustion_step : letI := limitCarrier.topologicalSpace
    ∀ j, closure (exhaustion j) ⊆ exhaustion (j + 1)
  /-- The domains cover the entire partial limit. -/
  exhaustion_covers : (⋃ j, exhaustion j) = univ
  /-- Total extensions of the source maps, meaningful on their stages. -/
  embedding : ∀ j, limitCarrier.carrier → M (subsequence j)
  /-- The source maps embed each open stage. -/
  embedding_open : letI := limitCarrier.topologicalSpace
    ∀ j, Topology.IsOpenEmbedding (fun x : exhaustion j => embedding j x)
  /-- They are actual smooth local diffeomorphisms on those stages. -/
  embedding_smooth : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    ∀ j, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (embedding j) (exhaustion j)
  /-- The selected source basepoint is preserved exactly. -/
  base_preserving : ∀ j, embedding j base = p (subsequence j)
  /-- Every derivative of the actual pulled-back metric converges on each
  compact subset of a chosen limit chart. -/
  metric_jets : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    ∀ q m K, IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ m ((g (subsequence j)).pullbackCoefficients
          (embedding j ∘ (extChartAt (𝓡 n) q).symm)))
        (iteratedFDeriv ℝ m (limitMetric.pullbackCoefficients
          (extChartAt (𝓡 n) q).symm)) atTop K
  /-- Every radius strictly below `A` is eventually separated from the
  boundary of some fixed stage in the actual source metrics. -/
  boundary_control : letI := limitCarrier.topologicalSpace
    ∀ B : ℝ, B < A → ∃ l : ℕ, ∀ᶠ j in atTop, ∀ q ∈ frontier (exhaustion l),
      ENNReal.ofReal B ≤ (g (subsequence j)).edist (p (subsequence j)) (embedding j q)

/-- Regard a partial limit of a strict subsequence as a partial limit of the
original source sequence; Theorem 5.6, printed pp. 85-87. -/
noncomputable def PartialPointedMetricConvergence.reindex
    {n : ℕ} {M : ℕ → Type u} [∀ k : ℕ, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (G : PartialPointedMetricConvergence (fun k => g (φ k)) (fun k => p (φ k)) A) :
    PartialPointedMetricConvergence g p A where
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
  boundary_control := G.boundary_control

end PoincareMT.M30
