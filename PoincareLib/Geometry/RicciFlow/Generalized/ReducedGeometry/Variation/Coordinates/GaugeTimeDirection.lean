import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic
import PoincareLib.Geometry.Spacetime.Realization.Interval.Topology
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Earlier times in actual compatible gauges

Morgan-Tian Definition 3.38 and Lemma 6.18, pp. 61, 113-114.
Boundary preservation and the actual normalized time tangent imply that
every gauge through a time with global past also contains past times.
A contrary least gauge endpoint would make the clock locally constant.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- If the global physical interval contains an earlier time, every
actual compatible gauge through the point contains an earlier time.
This is the boundary-sensitive local clock fact used in Lemma 6.18,
pp. 113-114, with Definition 3.38, p. 61. -/
theorem gauge_has_earlier_time (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) (hprev : ∃ a ∈ I.domain, a < t₀.val) :
    ∃ a ∈ (G.gaugeCover.interval b).domain, a < t₀.val := by
  by_contra hnone
  have hleast : IsLeast (G.gaugeCover.interval b).domain t₀.val := by
    refine ⟨t₀.property, ?_⟩
    intro a ha
    exact le_of_not_gt (fun hat => hnone ⟨a, ha, hat⟩)
  have htboundary : (𝓡∂ 1).IsBoundaryPoint t₀ := by
    change t₀ ∈ (𝓡∂ 1).boundary (G.timeIntervals.interval (G.gaugeCover.interval b)).Point
    rw [(G.timeIntervals.interval (G.gaugeCover.interval b)).boundary_eq]
    exact (Proofs.M11.interval_mem_frontier_iff (G.gaugeCover.interval b) t₀.property).mpr
      (Or.inl hleast)
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
  have hgreatest : IsGreatest I.domain t₀.val := by
    rcases (Proofs.M11.interval_mem_frontier_iff I htglobal).mp htfront with hmin | hmax
    · obtain ⟨a, ha, hat⟩ := hprev
      exact False.elim (not_lt_of_ge (hmin.2 ha) hat)
    · exact hmax
  have hopen := (G.gaugeCover.local_diffeomorph b).isOpen_range
  have hnear : range (G.gaugeCover.cylinder b).toSpacetime ∈ 𝓝 p :=
    hopen.mem_nhds ⟨(t₀, x₀), rfl⟩
  have hconstant : G.spacetime.timeFunction =ᶠ[𝓝 p] fun _ => t₀.val := by
    filter_upwards [hnear] with q hq
    obtain ⟨z, rfl⟩ := hq
    rw [(G.gaugeCover.cylinder b).time_eq]
    exact le_antisymm (hgreatest.2 ((G.gaugeCover.cylinder b).interval_subset z.1.property))
      (hleast.2 z.1.property)
  have hzero : mfderiv (spacetimeModel n) (𝓘(ℝ, ℝ)) G.spacetime.timeFunction p = 0 := by
    rw [hconstant.mfderiv_eq, mfderiv_const]
    rfl
  have hnorm := G.spacetime.timeVector_normalized p
  change mfderiv (spacetimeModel n) (𝓘(ℝ, ℝ)) G.spacetime.timeFunction p
    (G.spacetime.timeVector p) = 1 at hnorm
  rw [hzero] at hnorm
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hnorm

end PoincareMT.M14
