import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false
open Set
open scoped Topology
namespace Poincare.Topology

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

theorem mapsTo_frontier_connectedComponentIn_preimage_ball
    {X Y : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Continuous f) (p : X) (c : Y) (ρ : ℝ) :
    MapsTo f (frontier (connectedComponentIn (f ⁻¹' Metric.ball c ρ) p))
      (Metric.sphere c ρ) := by
  intro x hx
  exact Metric.frontier_ball_subset_sphere
    (hf.frontier_preimage_subset _ (frontier_connectedComponentIn_subset_of_isOpen
      (hf.isOpen_preimage _ Metric.isOpen_ball) p hx))

theorem dist_eq_of_mem_frontier_connectedComponentIn_preimage_ball
    {X Y : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : Continuous f) {p x : X} {c : Y} {ρ : ℝ}
    (hx : x ∈ frontier (connectedComponentIn (f ⁻¹' Metric.ball c ρ) p)) :
    dist (f x) c = ρ :=
  mapsTo_frontier_connectedComponentIn_preimage_ball hf p c ρ hx

end Poincare.Topology
