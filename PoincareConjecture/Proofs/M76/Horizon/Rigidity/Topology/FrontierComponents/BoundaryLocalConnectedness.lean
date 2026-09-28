import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClopenDomainFrontier

set_option autoImplicit false
open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}

theorem PLDomain.frontier_locallyPathConnectedSpace
    (he : PLDomain e R) (hR : IsCompact R) :
    LocallyPathConnectedSpace (frontier R) := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨s, f, K, A, H, g, HB, _, _, _, _, hA, _⟩ :=
      he.exists_original_frontier_surface_model hR hne
    let : LocallyPathConnectedSpace A.space := A.locallyPathConnectedSpace_of_finite hA
    exact HB.isQuotientMap.locallyPathConnectedSpace
  · have hzero : R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst R
    rw [frontier_empty]
    infer_instance

theorem PLDomain.isOpen_preimage_frontier_component
    (he : PLDomain e R) (hR : IsCompact R) {x : X} {S : Set X}
    (hx : x ∈ frontier R) (hcomponent : connectedComponentIn (frontier R) x = S) :
    IsOpen ((Subtype.val : frontier R → X) ⁻¹' S) := by
  let : LocallyPathConnectedSpace (frontier R) := he.frontier_locallyPathConnectedSpace hR
  rw [← hcomponent]
  exact Set.isOpen_preimage_connectedComponentIn hx

theorem PLDomain.isClopen_preimage_frontier_component
    (he : PLDomain e R) (hR : IsCompact R) {x : X} {S : Set X}
    (hx : x ∈ frontier R) (hcomponent : connectedComponentIn (frontier R) x = S) :
    IsClopen ((Subtype.val : frontier R → X) ⁻¹' S) := by
  refine ⟨?_, he.isOpen_preimage_frontier_component hR hx hcomponent⟩
  rw [← hcomponent, connectedComponentIn_eq_image hx,
    preimage_image_eq _ Subtype.coe_injective]
  exact isClosed_connectedComponent

end PoincareConjecture.M76
