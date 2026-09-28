import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Source.SourceModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.SelectedComponent

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem SourceDoubleComponents.exists_index_of_isolated_connected_set
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
    {S Q C : Set E} {R : Set X}
    (old : SourceDoubleComponents e f S Q R)
    (hC : IsCompact C) (hc : IsConnected C)
    (hsub : C ⊆ doubleLocusOn f S)
    (hrest : IsClosed (doubleLocusOn f S \ C)) :
    ∃ i : old.Index, old.pieces i = C := by
  classical
  let := old.finite_components
  obtain ⟨i,hi⟩ := hc.exists_closure_subset_of_finite_closed_cover old.pieces
    (fun i => (old.topology i).1.isClosed)
    (fun x hx => old.cover.subset (old.space.symm.subset (hsub hx)))
    (g := ∅) (fun i j hij => (disjoint_iff_inter_eq_empty.mp (old.disjoint hij)).subset)
    (disjoint_empty _)
  have hCi : C ⊆ old.pieces i := subset_closure.trans hi
  have hp : old.pieces i ⊆ C ∪ (doubleLocusOn f S \ C) := by
    intro x hx
    by_cases h : x ∈ C
    · exact Or.inl h
    · exact Or.inr ⟨old.piece_subset_double i hx,h⟩
  have hdis : Disjoint C (doubleLocusOn f S \ C) := disjoint_sdiff_right
  have hcase := isPreconnected_iff_subset_of_disjoint_closed.mp
    (old.topology i).2.1.isPreconnected C (doubleLocusOn f S \ C)
    hC.isClosed hrest hp (by rw [hdis.inter_eq,inter_empty])
  refine ⟨i,Subset.antisymm ?_ hCi⟩
  rcases hcase with h | h
  · exact h
  · obtain ⟨x,hx⟩ := hc.nonempty
    exact ((h (hCi hx)).2 hx).elim

theorem SourceDoubleComponents.mate_eq_of_literal_fibers
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
    {S Q D : Set E} {R : Set X}
    (old : SourceDoubleComponents e f S Q R) (i : old.Index)
    (hinj : InjOn f (old.pieces i)) (hDS : D ⊆ S)
    (hdis : Disjoint (old.pieces i) D)
    (hfull : ∀ x ∈ S, f x ∈ f '' old.pieces i ↔ x ∈ old.pieces i ∪ D) :
    old.mate i ≠ i ∧ old.pieces (old.mate i) = D := by
  have hmate : old.mate i ≠ i := by
    intro hm
    obtain ⟨x,hx⟩ := (old.topology i).2.1.nonempty
    have hxG := old.pieces_subset i hx
    have hp := (old.partner_component i ⟨x,hxG⟩).mp hx
    change (old.partner ⟨x,hxG⟩ : E) ∈ old.pieces (old.mate i) at hp
    rw [hm] at hp
    exact old.free ⟨x,hxG⟩ (hinj hp hx (old.value ⟨x,hxG⟩))
  refine ⟨hmate,Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hxS := (old.piece_subset_double (old.mate i) hx).1
    have him := (old.piece_image_preimage i x hxS).mpr (Or.inr hx)
    exact ((hfull x hxS).mp him).resolve_left
      (fun h => disjoint_left.mp (old.disjoint hmate) hx h)
  · intro x hx
    have him := (hfull x (hDS hx)).mpr (Or.inr hx)
    exact ((old.piece_image_preimage i x (hDS hx)).mp him).resolve_left
      (fun h => disjoint_left.mp hdis h hx)

end PoincareConjecture.M76.Dehn.Annuli
