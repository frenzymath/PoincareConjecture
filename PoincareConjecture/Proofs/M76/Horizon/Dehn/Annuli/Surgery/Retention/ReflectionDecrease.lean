import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ComponentCount

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem reflection_double_component_count_lt
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f g : E → X} {S T : Set E} (M : SourceCircleDecomposition f S) (i : M.Index)
    (htrace : doubleLocusOn f S ∩ T = M.pieces i)
    (hinside : M.pieces i ⊆ interior T)
    (hnew : doubleLocusOn g S = doubleLocusOn f (S \ interior T)) :
    Nat.card (ConnectedComponents (doubleLocusOn g S)) <
      Nat.card (ConnectedComponents (doubleLocusOn f S)) := by
  let K := S \ interior T
  have hi : Disjoint (M.pieces i) K := by
    apply disjoint_left.mpr
    exact fun x hx hk ↦ hk.2 (hinside hx)
  have hwhole : ∀ k, M.pieces k ⊆ K ∨ Disjoint (M.pieces k) K := by
    intro k
    by_cases hki : k = i
    · subst k
      exact Or.inr hi
    · apply Or.inl
      intro x hx
      refine ⟨M.piece_subset_source k hx, ?_⟩
      intro ht
      exact disjoint_left.mp (M.disjoint hki) hx
        (htrace.subset ⟨M.piece_subset_double k hx, interior_subset ht⟩)
  have hremoved : ¬ M.pieces i ⊆ K := by
    intro h
    obtain ⟨x, hx⟩ := (M.pieces_isConnected i).nonempty
    exact disjoint_left.mp hi hx (h hx)
  have hlocus : doubleLocusOn g S =
      (Subtype.val : K → E) '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y} := by
    rw [hnew]
    ext x
    constructor
    · rintro ⟨hx, y, hy, hxy, hne⟩
      exact ⟨⟨x, hx⟩, ⟨⟨y, hy⟩, hxy, hne⟩, rfl⟩
    · rintro ⟨x, ⟨y, hxy, hne⟩, rfl⟩
      exact ⟨x.property, y, y.property, hxy, hne⟩
  exact M.retained_component_count_lt sdiff_subset hwhole Subtype.val Subtype.val_injective
    continuous_subtype_val hlocus i hremoved

end PoincareConjecture.M76.Dehn.Annuli
