import PoincareConjecture.Definitions.M12GeneralizedEquation
import PoincareConjecture.Statements.M12MetricPredecessors












set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

namespace MovingSpacetimeGauge

theorem spatial_isEmbedding (e : MovingSpacetimeGauge F T C) (t : T.Point) :
    Topology.IsEmbedding (fun x : C ↦ e.toSpacetime (t, x)) :=
  e.embedding.comp (isEmbedding_prodMkRight t)

theorem source_t2Space (e : MovingSpacetimeGauge F T C) : T2Space C := by
  obtain ⟨t, ht⟩ := K.nontrivial.nonempty
  exact (e.spatial_isEmbedding ⟨t, ht⟩).t2Space

theorem source_secondCountableTopology (e : MovingSpacetimeGauge F T C) :
    SecondCountableTopology C := by
  obtain ⟨t, ht⟩ := K.nontrivial.nonempty
  exact (e.spatial_isEmbedding ⟨t, ht⟩).secondCountableTopology

end MovingSpacetimeGauge


theorem M12MetricPredecessors.exists_gaugeMetricLeviCivitaFamily
    (h : M12MetricPredecessors.{v} n) {e : MovingSpacetimeGauge F T C}
    (G : MovingSpacetimeGaugeGeometry e) : Nonempty (MetricLeviCivitaFamily G.metric) := by
  classical
  let : T2Space C := e.source_t2Space
  let : SecondCountableTopology C := e.source_secondCountableTopology
  exact ⟨fun t ↦ (h.connection_exists C (G.metric t)).some⟩

end PoincareConjecture
