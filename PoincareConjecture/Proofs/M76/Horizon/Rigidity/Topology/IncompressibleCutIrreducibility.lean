import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.IncompressibleBallAvoidance
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility













set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X ι σ : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R Ω : Set X}





theorem IsPLIrreducible.of_incompressible_cut
    (hΩ : IsPLIrreducible e Ω) (hR : PLDomain e R) (hRΩ : R ⊆ Ω)
    (M : σ → Set X) (hMfront : ∀ i, M i ⊆ frontier R)
    (hcut : ∀ x ∈ frontier R, x ∈ interior Ω → ∃ i, x ∈ M i)
    (hMconn : ∀ i, IsPreconnected (M i))
    (hpi : ∀ i (x : M i), Nontrivial (FundamentalGroup (M i) x) ∧
      Function.Injective (FundamentalGroup.map
        (ContinuousMap.inclusion
          ((hMfront i).trans (hR.closed.frontier_subset.trans hRΩ))) x)) :
    IsPLIrreducible e R := by
  refine ⟨hR, ?_⟩
  intro S hSR hs
  obtain ⟨s⟩ := hs
  have hSΩ : S ⊆ interior Ω := hSR.trans (interior_mono hRΩ)
  obtain ⟨D, hDΩ, ⟨b⟩⟩ := hΩ.2 S hSΩ ⟨s⟩
  have hDintΩ : D ⊆ interior Ω := b.subset_interior hDΩ hSΩ
  have hDM (i : σ) : Disjoint D (M i) := by
    apply b.disjoint_of_pi1_injective hDΩ
      ((hMfront i).trans (hR.closed.frontier_subset.trans hRΩ)) (hMconn i)
    · exact disjoint_interior_frontier.symm.mono (hMfront i) hSR
    · exact hpi i
  have hDfront : Disjoint D (frontier R) := by
    rw [Set.disjoint_left]
    intro x hxD hxfront
    obtain ⟨i, hxi⟩ := hcut x hxfront (hDintΩ hxD)
    exact Set.disjoint_left.mp (hDM i) hxD hxi
  have hDconn : IsPreconnected D := by
    rw [← b.closure_interior]
    exact b.isConnected_interior.isPreconnected.closure
  have hDintR : D ⊆ interior R := by
    apply hDconn.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨x, hx⟩ := s.isConnected.nonempty
      exact ⟨x, b.boundary_subset hx, hSR hx⟩
    · intro x hx
      have hxR : x ∈ R := by
        apply hR.closed.closure_eq.subset
        exact closure_mono interior_subset hx.1
      exact (mem_interior_iff_notMem_frontier hxR).mpr
        (fun hxf => Set.disjoint_left.mp hDfront hx.2 hxf)
  exact ⟨D, hDintR.trans interior_subset, ⟨b⟩⟩

end PoincareConjecture.M76
