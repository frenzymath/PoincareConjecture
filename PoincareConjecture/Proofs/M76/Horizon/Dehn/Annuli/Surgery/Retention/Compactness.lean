import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.DoubleLocusCopy

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli



theorem isCompact_retained_double_locus
    {E X : Type*} [TopologicalSpace E] {f : E → X} {K S : Set E}
    (hKS : K ⊆ S) (hK : IsClosed K) (hG : IsCompact (doubleLocusOn f S))
    (p : doubleLocusOn f S → doubleLocusOn f S) (hp : Continuous p)
    (hvalue : ∀ x, f (p x) = f x) (hfree : ∀ x, (p x : E) ≠ x)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E)) :
    IsCompact (doubleLocusOn f K) := by
  let G := doubleLocusOn f S
  let : CompactSpace G := isCompact_iff_compactSpace.mp hG
  let A : Set G := {x | (x : E) ∈ K ∧ (p x : E) ∈ K}
  have hA : IsClosed A := (hK.preimage continuous_subtype_val).inter
    (hK.preimage (continuous_subtype_val.comp hp))
  have heq : (Subtype.val : G → E) '' A = doubleLocusOn f K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.1, p z, hz.2, (hvalue z).symm, Ne.symm (hfree z)⟩
    · rintro ⟨hx, y, hy, hxy, hne⟩
      let z : G := ⟨x, hKS hx, y, hKS hy, hxy, hne⟩
      have hyval := hunique z y (hKS hy) hxy hne
      exact ⟨z, ⟨hx, hyval ▸ hy⟩, rfl⟩
  rw [← heq]
  exact hA.isCompact.image continuous_subtype_val



theorem isCompact_new_double_locus_of_retained
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {f : E → X} {g : Y → X} {K S : Set E} {T : Set Y}
    (hKS : K ⊆ S) (hK : IsClosed K) (hG : IsCompact (doubleLocusOn f S))
    (p : doubleLocusOn f S → doubleLocusOn f S) (hp : Continuous p)
    (hvalue : ∀ x, f (p x) = f x) (hfree : ∀ x, (p x : E) ≠ x)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E))
    (j : K → Y) (hj : Continuous j)
    (hnew : doubleLocusOn g T =
      j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y}) :
    IsCompact (doubleLocusOn g T) := by
  have hcompact := isCompact_retained_double_locus hKS hK hG p hp hvalue hfree hunique
  let : CompactSpace (doubleLocusOn f K) := isCompact_iff_compactSpace.mp hcompact
  have hsub : doubleLocusOn f K ⊆ K := fun _ hx ↦ hx.1
  let J : doubleLocusOn f K → Y := j ∘ Set.inclusion hsub
  have hJ : Continuous J := hj.comp (continuous_inclusion hsub)
  have hrange : range J = doubleLocusOn g T := by
    rw [hnew]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy, hxy, hne⟩ := x.property.2
      exact ⟨⟨x, x.property.1⟩, ⟨⟨y, hy⟩, hxy, hne⟩, rfl⟩
    · rintro ⟨x, ⟨y, hxy, hne⟩, rfl⟩
      exact ⟨⟨x, x.property, y, y.property, hxy, hne⟩, rfl⟩
  rw [← hrange]
  exact isCompact_range hJ

end PoincareConjecture.M76.Dehn.Annuli
