import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricConvergence
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.MetricConvergence

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}

def toM28 (G : PartialPointedMetricConvergence g p A) :
    M28.PartialPointedMetricConvergence g p A where
  limitCarrier := G.limitCarrier
  limitMetric := G.limitMetric
  base := G.base
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
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

def ofM28 (G : M28.PartialPointedMetricConvergence g p A) :
    PartialPointedMetricConvergence g p A where
  limitCarrier := G.limitCarrier
  limitMetric := G.limitMetric
  base := G.base
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
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

end PoincareConjecture.M30.PartialPointedMetricConvergence
