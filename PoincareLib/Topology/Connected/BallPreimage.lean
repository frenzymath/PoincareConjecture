import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Frontiers of components of ball preimages

In a locally connected source, the frontier of a component of an open set
lies in the frontier of that open set. For the preimage of a metric ball
under a continuous map, its component frontier therefore maps to the sphere.
The target may be pseudometric, and the frontier statement needs no
positivity assumption on the radius.
-/

set_option autoImplicit false
open Set
open scoped Topology
namespace Poincare.Topology

/-- A component of an open set has no frontier points inside that open set
in a locally connected space. -/
theorem frontier_connectedComponentIn_subset_of_isOpen
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {O : Set X} (hO : IsOpen O) (p : X) :
    frontier (connectedComponentIn O p) ⊆ frontier O := by
  intro x hx
  refine ⟨closure_mono (connectedComponentIn_subset O p) hx.1, ?_⟩
  intro hxi
  have hxO : x ∈ O := interior_subset hxi
  have hV := hO.connectedComponentIn (x := x)
  have hxV := mem_connectedComponentIn hxO
  obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hx.1 _ hV hxV
  have hxC : x ∈ connectedComponentIn O p := by
    rw [connectedComponentIn_eq hzC, ← connectedComponentIn_eq hzV]
    exact hxV
  exact hx.2 (hO.connectedComponentIn.interior_eq.symm ▸ hxC)

/-- The frontier of a component of a ball preimage maps to the corresponding
metric sphere. -/
theorem mapsTo_frontier_connectedComponentIn_preimage_ball
    {X Y : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Continuous f) (p : X) (c : Y) (ρ : ℝ) :
    MapsTo f (frontier (connectedComponentIn (f ⁻¹' Metric.ball c ρ) p))
      (Metric.sphere c ρ) := by
  intro x hx
  exact Metric.frontier_ball_subset_sphere
    (hf.frontier_preimage_subset _ (frontier_connectedComponentIn_subset_of_isOpen
      (hf.isOpen_preimage _ Metric.isOpen_ball) p hx))

/-- Every frontier point of a ball-preimage component has image distance
exactly equal to the ball radius. -/
theorem dist_eq_of_mem_frontier_connectedComponentIn_preimage_ball
    {X Y : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Continuous f) {p x : X} {c : Y} {ρ : ℝ}
    (hx : x ∈ frontier (connectedComponentIn (f ⁻¹' Metric.ball c ρ) p)) :
    dist (f x) c = ρ :=
  mapsTo_frontier_connectedComponentIn_preimage_ball hf p c ρ hx

end Poincare.Topology

