import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.DoubleLocusCopy

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli



theorem exists_retained_open_source_copy
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y] [T2Space Y]
    {f : E → X} {g : Y → X} {K S B : Set E} {T C : Set Y}
    (hKS : K ⊆ S) (hK : IsCompact K) (hB : IsClosed B) (hC : IsClosed C)
    (j : K → Y) (hj : Function.Injective j) (hc : Continuous j)
    (hmaps : ∀ x, j x ∈ T) (hkeep : ∀ x, g (j x) = f x)
    (holdcover : S ⊆ K ∪ B) (hnewcover : T ⊆ range j ∪ C)
    (hcontact : ∀ x : K, j x ∈ C → (x : E) ∈ B)
    (havoid : ∀ x : K, (x : E) ∈ doubleLocusOn f S → (x : E) ∉ B)
    (hnew : doubleLocusOn g T =
      j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y}) :
    ∃ (U : Set E) (V : Set Y) (H : U ≃ₜ V),
      U ⊆ K ∧ V ⊆ T ∧
      IsOpen ((Subtype.val : S → E) ⁻¹' U) ∧
      IsOpen ((Subtype.val : T → Y) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : E) ∈ K, (H x : Y) = j ⟨x, hx⟩) ∧
      (∀ x : U, g (H x) = f x) ∧
      (∀ x : K, (x : E) ∈ doubleLocusOn f S → (x : E) ∈ U) ∧
      doubleLocusOn g T ⊆ V := by
  let U : Set E := S \ B
  have hUK : U ⊆ K := fun x hx ↦ (holdcover hx.1).resolve_right hx.2
  let J : U → Y := fun x ↦ j ⟨x, hUK x.property⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hj' : IsClosedEmbedding j := hc.isClosedEmbedding hj
  have hJ : IsEmbedding J := hj'.isEmbedding.comp (IsEmbedding.inclusion hUK)
  have hseam : IsClosed (j '' ((Subtype.val : K → E) ⁻¹' B)) :=
    hj'.isClosedMap _ (hB.preimage continuous_subtype_val)
  have hrange : range J = T \ (C ∪ j '' ((Subtype.val : K → E) ⁻¹' B)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨hmaps _, ?_⟩
      rintro (hc' | ⟨z, hz, heq⟩)
      · exact x.property.2 (hcontact _ hc')
      · have heq' : z = ⟨x, hUK x.property⟩ := hj heq
        exact x.property.2 ((congrArg (fun t : K ↦ (t : E) ∈ B) heq').mp hz)
    · rintro ⟨hy, hoff⟩
      rcases hnewcover hy with ⟨x, rfl⟩ | hc'
      · have hxB : (x : E) ∉ B := fun hx ↦ hoff (Or.inr ⟨x, hx, rfl⟩)
        exact ⟨⟨x, hKS x.property, hxB⟩, rfl⟩
      · exact False.elim (hoff (Or.inl hc'))
  refine ⟨U, range J, hJ.toHomeomorph, hUK, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hmaps _
  · have heq : (Subtype.val : S → E) ⁻¹' U =
        ((Subtype.val : S → E) ⁻¹' B)ᶜ := by
      ext x
      exact and_iff_right x.property
    rw [heq]
    exact (hB.preimage continuous_subtype_val).isOpen_compl
  · have heq : (Subtype.val : T → Y) ⁻¹' range J =
        ((Subtype.val : T → Y) ⁻¹' (C ∪ j '' ((Subtype.val : K → E) ⁻¹' B)))ᶜ := by
      rw [hrange]
      ext x
      exact and_iff_right x.property
    rw [heq]
    exact ((hC.union hseam).preimage continuous_subtype_val).isOpen_compl
  · intro x
    exact ⟨hUK x.property, rfl⟩
  · intro x
    exact hkeep _
  · intro x hx
    exact ⟨hKS x.property, havoid x hx⟩
  · intro y hy
    obtain ⟨x, ⟨z, hxz, hne⟩, rfl⟩ := hnew.subset hy
    have hx : (x : E) ∈ U := ⟨hKS x.property,
      havoid x ⟨hKS x.property, z, hKS z.property, hxz, hne⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩

end PoincareConjecture.M76.Dehn.Annuli
