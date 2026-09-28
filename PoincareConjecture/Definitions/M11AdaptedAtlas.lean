import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open scoped ContDiff Topology

universe u

namespace PoincareConjecture


structure SpacetimeInterval where
  domain : Set ℝ
  ordConnected : domain.OrdConnected
  nontrivial : domain.Nontrivial


structure AdaptedMetricBox (n : ℕ) (X : Type u) [TopologicalSpace X]
    (time : X → ℝ) (I : SpacetimeInterval) where
  interval : SpacetimeInterval
  spatial : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))
  spatial_nonempty : (spatial : Set (EuclideanSpace ℝ (Fin n))).Nonempty
  interval_relatively_open :
    ∃ U : Set ℝ, IsOpen U ∧ interval.domain = I.domain ∩ U
  toSpacetime : interval.domain × spatial → X
  openEmbedding : Topology.IsOpenEmbedding toSpacetime
  time_toSpacetime : ∀ p, time (toSpacetime p) = p.1.1
  metric : ℝ × EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
  metric_smooth : ContDiffOn ℝ ∞ metric
    (interval.domain ×ˢ (spatial : Set (EuclideanSpace ℝ (Fin n))))
  metric_symm : ∀ t ∈ interval.domain, ∀ x ∈ spatial, ∀ v w,
    metric (t, x) v w = metric (t, x) w v
  metric_pos : ∀ t ∈ interval.domain, ∀ x ∈ spatial, ∀ v, v ≠ 0 →
    0 < metric (t, x) v v


theorem AdaptedMetricBox.interval_subset {n : ℕ} {X : Type u}
    [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    (b : AdaptedMetricBox n X time I) : b.interval.domain ⊆ I.domain := by
  rcases b.interval_relatively_open with ⟨U, _, hU⟩
  rw [hU]
  exact Set.inter_subset_left



structure AdaptedMetricTransition {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval}
    (b c : AdaptedMetricBox n X time I)
    (t : ℝ) (x y : EuclideanSpace ℝ (Fin n)) where
  interval : SpacetimeInterval
  interval_relatively_open :
    ∃ U : Set ℝ, IsOpen U ∧ interval.domain = I.domain ∩ U
  interval_subset_left : interval.domain ⊆ b.interval.domain
  interval_subset_right : interval.domain ⊆ c.interval.domain
  time_mem : t ∈ interval.domain
  coordinateChange : OpenPartialHomeomorph
    (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  source_subset : coordinateChange.source ⊆ b.spatial
  target_subset : coordinateChange.target ⊆ c.spatial
  source_mem : x ∈ coordinateChange.source
  map_marked : coordinateChange x = y
  smooth : ContDiffOn ℝ ∞ coordinateChange coordinateChange.source
  symm_smooth : ContDiffOn ℝ ∞ coordinateChange.symm coordinateChange.target
  box_eq : ∀ s (hs : s ∈ interval.domain),
    ∀ z (hz : z ∈ coordinateChange.source),
      b.toSpacetime
          (⟨s, interval_subset_left hs⟩, ⟨z, source_subset hz⟩) =
        c.toSpacetime
          (⟨s, interval_subset_right hs⟩,
            ⟨coordinateChange z, target_subset (coordinateChange.map_source hz)⟩)
  metric_eq : ∀ s ∈ interval.domain, ∀ z ∈ coordinateChange.source, ∀ v w,
    b.metric (s, z) v w =
      c.metric (s, coordinateChange z)
        (fderiv ℝ coordinateChange z v) (fderiv ℝ coordinateChange z w)



structure AdaptedMetricAtlas (n : ℕ) (X : Type u) [TopologicalSpace X] where
  time : X → ℝ
  interval : SpacetimeInterval
  time_continuous : Continuous time
  time_range : Set.range time = interval.domain
  box_index : Type u
  box : box_index → AdaptedMetricBox n X time interval
  box_covers : ∀ p : X, ∃ b, ∃ q, (box b).toSpacetime q = p
  transitions : ∀ b c, ∀ t,
    ∀ (hb : t ∈ (box b).interval.domain) (hc : t ∈ (box c).interval.domain),
    ∀ (x : (box b).spatial) (y : (box c).spatial),
      (box b).toSpacetime (⟨t, hb⟩, x) =
        (box c).toSpacetime (⟨t, hc⟩, y) →
      Nonempty (AdaptedMetricTransition (box b) (box c) t x y)

end PoincareConjecture
