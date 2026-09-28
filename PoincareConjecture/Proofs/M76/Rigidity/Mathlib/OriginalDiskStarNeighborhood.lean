import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalStarNeighborhood

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X] [TopologicalSpace V]

theorem exists_original_open_neighborhood_inside_closedStar
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set X} (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (hpC : (g p : X) ∈ interior C)
    (B : OpenPartialHomeomorph X V)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source) :
    InjOn (fun z => B (g z)) (K.closedStar p).space ∧
      (∃ O : Set X, IsOpen O ∧ (g p : X) ∈ O ∧ O ⊆ B.source ∧
        O ⊆ (fun z => (g z : X)) '' (K.closedStar p).space) ∧
      B (g p) ∈ interior ((fun z => B (g z)) '' (K.closedStar p).space) := by
  obtain ⟨hinj, U, hU, hpU, hUB, hUC⟩ :=
    K.exists_original_open_neighborhood_of_closedStar hK H g hg hp B hsource
  let O := U ∩ interior C
  have hO : IsOpen O := hU.inter isOpen_interior
  have hpO : (g p : X) ∈ O := ⟨hpU, hpC⟩
  have hOB : O ⊆ B.source := fun _ hx => hUB hx.1
  have hOS : O ⊆ (fun z => (g z : X)) '' (K.closedStar p).space :=
    fun _ hx => hUC ⟨hx.1, interior_subset hx.2⟩
  refine ⟨hinj, ⟨O, hO, hpO, hOB, hOS⟩, ?_⟩
  have himage : B '' O ⊆ (fun z => B (g z)) '' (K.closedStar p).space := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hOS hx
    exact ⟨z, hz, congrArg B hzx⟩
  exact interior_maximal himage (B.isOpen_image_of_subset_source hO hOB)
    (mem_image_of_mem B hpO)

end Geometry.SimplicialComplex
