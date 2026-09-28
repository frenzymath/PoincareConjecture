import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility
import PoincareConjecture.Proofs.M76.Mathlib.PlanarRegionSideTransport

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

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

end PoincareConjecture.M76
