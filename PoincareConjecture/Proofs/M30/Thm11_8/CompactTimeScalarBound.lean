import PoincareConjecture.Proofs.M30.Thm11_8.CompactScalarComparison
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteDistance
import PoincareConjecture.Proofs.M30.Thm11_8.CompactScalarAnchor
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_compact_scalar_bound_of_anchors_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ),
        0 < epsilon → epsilon ≤ epsilon0 → 0 < C →
        GeneralizedBoundedDistanceHypotheses S epsilon C →
      ∀ (T : ℝ), 0 < T →
      ∀ (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
        (X : Set G.limit.carrier.carrier),
        IsCompact X → IsConnected X →
      ∀ Cmin : ℝ,
        (∀ t ∈ Ioc (-T) 0, ∃ y ∈ X,
          (G.limit.flow.connection t).scalarCurvature y ≤ Cmin) →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (-T) 0, ∀ x ∈ X,
          (G.limit.flow.connection t).scalarCurvature x ≤ B := by
  obtain ⟨epsilon0, hepsilon0, hepsilonMax, hcomparison⟩ :=
    exists_compact_limit_scalar_bound_threshold P
  refine ⟨epsilon0, hepsilon0, hepsilonMax, ?_⟩
  intro S epsilon C hepsilon hepsilonLe hC H T hT G X hX hXconnected Cmin hmin
  let g := G.limit.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  obtain ⟨r, hr, hball⟩ := hX.isBounded.subset_ball_lt 0 G.limit.base
  obtain ⟨D, _hD, hdist⟩ := exists_finite_limit_distance_error P.m04 P.m06 G.limit
  apply hcomparison S epsilon C hepsilon hepsilonLe hC H T hT G X
    hX hXconnected (2 * r + D) Cmin _ hmin
  intro t ht x hx y hy
  have hxball : dist x G.limit.base < r := hball hx
  have hyball : dist y G.limit.base < r := hball hy
  have hterminal : (g.edist x y).toReal ≤ 2 * r := by
    change dist x y ≤ 2 * r
    exact (dist_triangle_right x y G.limit.base).trans
      (by linarith)
  exact (hdist t ht x y).2.trans (add_le_add hterminal le_rfl)

theorem exists_compact_limit_uniform_scalar_bound_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ),
        0 < epsilon → epsilon ≤ epsilon0 → 0 < C →
        GeneralizedBoundedDistanceHypotheses S epsilon C →
      ∀ (T : ℝ), 0 < T →
      ∀ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
        IsCompact (univ : Set G.limit.carrier.carrier) →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (-T) 0,
          ∀ x : G.limit.carrier.carrier,
            (G.limit.flow.connection t).scalarCurvature x ≤ B := by
  obtain ⟨epsilon0, hepsilon0, hepsilonMax, hbound⟩ :=
    exists_compact_scalar_bound_of_anchors_threshold P
  refine ⟨epsilon0, hepsilon0, hepsilonMax, ?_⟩
  intro S epsilon C hepsilon hepsilonLe hC H T hT G hcompact
  let : CompactSpace G.limit.carrier.carrier := isCompact_univ_iff.mp hcompact
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  have hanchors : ∀ t ∈ Ioc (-T) 0, ∃ y ∈ (univ : Set G.limit.carrier.carrier),
      (G.limit.flow.connection t).scalarCurvature y ≤ 1 := by
    intro t ht
    obtain ⟨y, hy⟩ := exists_compact_limit_scalar_anchor P.m04 G.limit t ht
    exact ⟨y, mem_univ y, hy⟩
  obtain ⟨B, hB, hscalar⟩ := hbound S epsilon C hepsilon hepsilonLe hC H T hT G univ
    hcompact isConnected_univ 1 hanchors
  exact ⟨B, hB, fun t ht x => hscalar t ht x (mem_univ x)⟩

end PoincareConjecture.M30
