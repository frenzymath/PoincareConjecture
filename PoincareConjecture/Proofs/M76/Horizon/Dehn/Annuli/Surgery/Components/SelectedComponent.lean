import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.Decomposition



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.SourceCircleDecomposition

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → X} {S : Set E}

open Classical in
abbrev Index (D : SourceCircleDecomposition f S) :=
  D.graph.vertexAbstractComplex.edgeGraph.ConnectedComponent

instance (D : SourceCircleDecomposition f S) : Finite D.Index := D.finite_components

def pieces (D : SourceCircleDecomposition f S) (i : D.Index) : Set E :=
  (D.polygon i).boundary ℝ

theorem piece_subset_double (D : SourceCircleDecomposition f S) (i : D.Index) :
    D.pieces i ⊆ doubleLocusOn f S := by
  intro x hx
  exact D.space.subset (D.cover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩))

theorem piece_subset_source (D : SourceCircleDecomposition f S) (i : D.Index) :
    D.pieces i ⊆ S := fun _ hx ↦ (D.piece_subset_double i hx).1

theorem piece_image_preimage (D : SourceCircleDecomposition f S) (i : D.Index)
    (x : E) (hx : x ∈ S) :
    f x ∈ f '' D.pieces i ↔ x ∈ D.pieces i ∪ D.pieces (D.mate i) := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_cases hxy : y = x
    · exact Or.inl (hxy ▸ hy)
    · have hyG : y ∈ D.graph.space := D.space.symm.subset (D.piece_subset_double i hy)
      have heq := D.unique ⟨y, hyG⟩ x hx hxy hyx
      exact Or.inr (heq.symm ▸ (D.partner_component i ⟨y, hyG⟩).mp hy)
  · rintro (hxi | hxm)
    · exact ⟨x, hxi, rfl⟩
    · exact (D.image_mate i).subset ⟨x, hxm, rfl⟩

theorem pieces_isCompact (D : SourceCircleDecomposition f S) (i : D.Index) :
    IsCompact (D.pieces i) := (D.topology i).1

theorem pieces_isConnected (D : SourceCircleDecomposition f S) (i : D.Index) :
    IsConnected (D.pieces i) := (D.topology i).2.1



theorem source_preimage_piece_image (D : SourceCircleDecomposition f S) (i : D.Index) :
    S ∩ f ⁻¹' (f '' D.pieces i) = D.pieces i ∪ D.pieces (D.mate i) := by
  ext x
  constructor
  · exact fun hx ↦ (D.piece_image_preimage i x hx.1).mp hx.2
  · intro hx
    have hxS : x ∈ S := hx.elim (fun h ↦ D.piece_subset_source i h)
      (fun h ↦ D.piece_subset_source (D.mate i) h)
    exact ⟨hxS, (D.piece_image_preimage i x hxS).mpr hx⟩

end PoincareConjecture.M76.Dehn.Annuli.SourceCircleDecomposition
