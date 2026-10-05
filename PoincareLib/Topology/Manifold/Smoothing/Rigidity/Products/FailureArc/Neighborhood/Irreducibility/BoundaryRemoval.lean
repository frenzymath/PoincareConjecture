import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallTopology
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLIrreducibility
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.PlanarRegionSideTransport

/-!
# Irreducibility after removing a connected boundary-attached set

A filling sphere in the retained interior misses the removed set. Its
original filling ball also misses that set: connectedness transports the
side of the sphere from a point on the original domain frontier.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

/-- Removing a preconnected set meeting the old frontier preserves
irreducibility whenever the retained set is an actual original PL domain. -/
theorem IsPLIrreducible.sdiff_of_preconnected_boundary_meeting
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R U : Set X}
    (hI : IsPLIrreducible e R) (he : PLDomain e (R \ U))
    (hU : IsPreconnected U) (hmeet : (U ∩ frontier R).Nonempty) :
    IsPLIrreducible e (R \ U) := by
  refine ⟨he, ?_⟩
  intro S hSQ hs
  have hSR : S ⊆ interior R := hSQ.trans (interior_mono sdiff_subset)
  obtain ⟨D, hDR, ⟨ball⟩⟩ := hI.2 S hSR hs
  have hDint : D ⊆ interior R := ball.subset_interior hDR hSR
  have havoid : Disjoint U (frontier D) := by
    rw [ball.frontier_eq]
    exact disjoint_left.mpr (fun x hxU hxS => (interior_subset (hSQ hxS)).2 hxU)
  obtain ⟨x, hxU, hxR⟩ := hmeet
  have hxD : x ∉ D := fun hx => hxR.2 (hDint hx)
  refine ⟨D, ?_, ⟨ball⟩⟩
  intro y hyD
  refine ⟨hDR hyD, ?_⟩
  intro hyU
  exact hxD ((hU.mem_iff_of_disjoint_frontier havoid hxU hyU).mpr hyD)

end PoincareMT.M76
