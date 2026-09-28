import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.IrreducibleSphericalBoundaryComponent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.SelectedComponentBoundaries
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.SphereClopen








set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem nonempty_original_ball_of_selected_boundary_sphere
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q S : Set X}
    (hQ : IsCompact Q) (hI : IsPLIrreducible e Q)
    (hSQ : S ⊆ frontier Q)
    (hclopen : IsClopen ((Subtype.val : frontier Q → X) ⁻¹' S))
    (sph : ChartwisePLSphere e S) (x : X) (hx : x ∈ S) :
    let P := connectedComponentIn Q x
    IsCompact P ∧ PLDomain e P ∧ IsConnected P ∧ IsPLIrreducible e P ∧
      S ⊆ P ∧ P ⊆ Q ∧ frontier P = S ∧ P ∩ frontier Q = S ∧
      Nonempty (ChartwisePLBall e P S) ∧
      ∀ y ∈ P, connectedComponentIn Q y = P := by
  dsimp only
  have hSQ' : S ⊆ Q := hSQ.trans hI.1.closed.frontier_subset
  have hxQ := hSQ' hx
  have hcompact := Set.isCompact_connectedComponentIn_of_mem hQ hxQ
  have hcomponent := hI.connectedComponentIn hQ hxQ
  have hconnected := isConnected_connectedComponentIn_iff.mpr hxQ
  have hSP : S ⊆ connectedComponentIn Q x :=
    sph.isConnected.isPreconnected.subset_connectedComponentIn hx hSQ'
  have hfront := hI.1.frontier_connectedComponentIn_of_compact hQ hxQ
  have hSPfront : S ⊆ frontier (connectedComponentIn Q x) := by
    rw [hfront]
    exact subset_inter hSP hSQ
  have hclopen' : IsClopen
      ((Subtype.val : frontier (connectedComponentIn Q x) → X) ⁻¹' S) := by
    let inc : frontier (connectedComponentIn Q x) → frontier Q :=
      Set.inclusion (fun _ hz ↦ (hfront.subset hz).2)
    exact hclopen.preimage (show Continuous inc from continuous_inclusion _)
  obtain ⟨hboundary, hball⟩ := hcomponent.nonempty_ball_of_spherical_boundary_component
    hcompact hconnected hSPfront hclopen' sph
  exact ⟨hcompact, hcomponent.1, hconnected, hcomponent, hSP,
    connectedComponentIn_subset Q x, hboundary, hfront.symm.trans hboundary, hball,
    fun _ hy ↦ (connectedComponentIn_eq hy).symm⟩

theorem nonempty_original_ball_of_boundary_sphere
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q S : Set X}
    (hQ : IsCompact Q) (hI : IsPLIrreducible e Q)
    (hSQ : S ⊆ frontier Q) (sph : ChartwisePLSphere e S) (x : X) (hx : x ∈ S) :
    let P := connectedComponentIn Q x
    IsCompact P ∧ PLDomain e P ∧ IsConnected P ∧ IsPLIrreducible e P ∧
      S ⊆ P ∧ P ⊆ Q ∧ frontier P = S ∧ P ∩ frontier Q = S ∧
      Nonempty (ChartwisePLBall e P S) ∧
      ∀ y ∈ P, connectedComponentIn Q y = P :=
  nonempty_original_ball_of_selected_boundary_sphere hQ hI hSQ
    (sph.isClopen_in_frontier hI.1 hSQ) sph x hx

end PoincareConjecture.M76.Dehn.Annuli
