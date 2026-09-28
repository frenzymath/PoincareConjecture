import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.Counts



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
  {S Q : Set E} {R : Set X}

theorem SourceDoubleComponents.piece_subset_double
    (M : SourceDoubleComponents e f S Q R) (i : M.Index) :
    M.pieces i ⊆ doubleLocusOn f S := (M.pieces_subset i).trans M.space.subset

theorem SourceDoubleComponents.injOn_piece_of_mate_ne
    (M : SourceDoubleComponents e f S Q R) (i : M.Index) (hi : M.mate i ≠ i) :
    InjOn f (M.pieces i) := by
  intro x hx y hy hxy
  by_contra hne
  have hp := M.unique ⟨x, M.pieces_subset i hx⟩ y
    (M.piece_subset_double i hy).1 hne hxy
  exact disjoint_left.mp (M.disjoint hi)
    ((M.partner_component i ⟨x, M.pieces_subset i hx⟩).mp hx) (hp ▸ hy)

theorem SourceDoubleComponents.piece_image_preimage
    (M : SourceDoubleComponents e f S Q R) (i : M.Index) (x : E) (hx : x ∈ S) :
    f x ∈ f '' M.pieces i ↔ x ∈ M.pieces i ∪ M.pieces (M.mate i) := by
  constructor
  · rintro ⟨y, hy, hfy⟩
    by_cases hyx : y = x
    · exact Or.inl (hyx ▸ hy)
    · have h := M.unique ⟨y, M.pieces_subset i hy⟩ x hx hyx hfy
      exact Or.inr (h.symm ▸ (M.partner_component i ⟨y, M.pieces_subset i hy⟩).mp hy)
  · rintro (hi | hm)
    · exact ⟨x, hi, rfl⟩
    · exact M.image_mate i ▸ mem_image_of_mem f hm

end PoincareConjecture.M76.Dehn.Annuli

