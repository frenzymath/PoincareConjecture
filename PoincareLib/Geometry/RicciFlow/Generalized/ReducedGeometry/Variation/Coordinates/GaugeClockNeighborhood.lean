import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeTimeDirection
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.IntervalRelativeNeighborhood

/-!
# Relative physical clock neighborhoods in actual gauges

Morgan-Tian Definition 3.38 and Lemma 6.18, pp. 61, 113-114.
Boundary preservation and the normalized actual time vector also
force every available future direction into the gauge. Its interval
therefore contains a relative physical neighborhood at every point.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- Every global later time direction is present in a compatible
gauge through the point. A contrary boundary orientation would make
the actual normalized clock locally constant, Definition 3.38 and
Lemma 6.18, pp. 61, 113-114. -/
theorem gauge_has_later_time (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) (hnext : ∃ a ∈ I.domain, t₀.val < a) :
    ∃ a ∈ (G.gaugeCover.interval b).domain, t₀.val < a := by
  by_contra hnone
  have hgreatest : IsGreatest (G.gaugeCover.interval b).domain t₀.val := by
    refine ⟨t₀.property, ?_⟩
    intro a ha
    exact le_of_not_gt (fun hat => hnone ⟨a, ha, hat⟩)
  have htboundary : (𝓡∂ 1).IsBoundaryPoint t₀ := by
    change t₀ ∈ (𝓡∂ 1).boundary (G.timeIntervals.interval (G.gaugeCover.interval b)).Point
    rw [(G.timeIntervals.interval (G.gaugeCover.interval b)).boundary_eq]
    exact (Proofs.M11.interval_mem_frontier_iff (G.gaugeCover.interval b) t₀.property).mpr
      (Or.inr hgreatest)
  have hpairboundary : (spacetimeModel n).IsBoundaryPoint (t₀, x₀) := by
    change (t₀, x₀) ∈ ((𝓡∂ 1).prod (𝓡 n)).boundary _
    rw [ModelWithCorners.boundary_prod]
    exact Or.inr ⟨htboundary, mem_univ _⟩
  let p := (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)
  have hpboundary : (spacetimeModel n).IsBoundaryPoint p :=
    ((G.gaugeCover.local_diffeomorph b (t₀, x₀)).isBoundaryPoint_iff (by simp)).mp hpairboundary
  have hclock : G.spacetime.timeFunction p = t₀.val := (G.gaugeCover.cylinder b).time_eq _
  have htglobal : t₀.val ∈ I.domain :=
    (G.gaugeCover.cylinder b).interval_subset t₀.property
  have htfront : t₀.val ∈ frontier I.domain := by
    change p ∈ (spacetimeModel n).boundary G.Point at hpboundary
    rw [G.spacetime.boundary_eq] at hpboundary
    exact hclock ▸ hpboundary
  have hleast : IsLeast I.domain t₀.val := by
    rcases (Proofs.M11.interval_mem_frontier_iff I htglobal).mp htfront with hmin | hmax
    · exact hmin
    · obtain ⟨a, ha, hat⟩ := hnext
      exact False.elim (not_lt_of_ge (hmax.2 ha) hat)
  have hopen := (G.gaugeCover.local_diffeomorph b).isOpen_range
  have hnear : range (G.gaugeCover.cylinder b).toSpacetime ∈ 𝓝 p :=
    hopen.mem_nhds ⟨(t₀, x₀), rfl⟩
  have hconstant : G.spacetime.timeFunction =ᶠ[𝓝 p] fun _ => t₀.val := by
    filter_upwards [hnear] with q hq
    obtain ⟨z, rfl⟩ := hq
    rw [(G.gaugeCover.cylinder b).time_eq]
    exact le_antisymm (hgreatest.2 z.1.property)
      (hleast.2 ((G.gaugeCover.cylinder b).interval_subset z.1.property))
  have hzero : mfderiv (spacetimeModel n) (𝓘(ℝ, ℝ)) G.spacetime.timeFunction p = 0 := by
    rw [hconstant.mfderiv_eq, mfderiv_const]
    rfl
  have hnorm := G.spacetime.timeVector_normalized p
  change mfderiv (spacetimeModel n) (𝓘(ℝ, ℝ)) G.spacetime.timeFunction p
    (G.spacetime.timeVector p) = 1 at hnorm
  rw [hzero] at hnorm
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hnorm

/-- A compatible gauge contains a relative physical clock neighborhood
of each of its points, including physical endpoints, Definition 3.38
and Lemma 6.18, pp. 61, 113-114. -/
theorem gauge_timeDomain_mem_nhdsWithin (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) :
    (G.gaugeCover.interval b).domain ∈ 𝓝[I.domain] t₀.val :=
  ordConnected_mem_nhdsWithin_of_directions (G.gaugeCover.interval b).ordConnected
    t₀.property (gauge_has_earlier_time b t₀ x₀) (gauge_has_later_time b t₀ x₀)

/-- Physical admissibility and square-clock continuity pull a gauge
clock neighborhood back to the same actual within parameter set,
the local clock control for Lemma 6.18, pp. 113-114. -/
theorem gauge_squareClock_mem_nhdsWithin (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {T s : ℝ} {C : Set ℝ}
    (hclock : T - s ^ 2 = t₀.val) (htime : ∀ r ∈ C, T - r ^ 2 ∈ I.domain) :
    {r | T - r ^ 2 ∈ (G.gaugeCover.interval b).domain} ∈ 𝓝[C] s := by
  have hc : ContinuousWithinAt (fun r : ℝ => T - r ^ 2) C s :=
    (continuous_const.sub (continuous_id.pow 2)).continuousWithinAt
  have ht := hc.tendsto_nhdsWithin htime
  rw [hclock] at ht
  exact ht.eventually (gauge_timeDomain_mem_nhdsWithin b t₀ x₀)

end PoincareMT.M14
