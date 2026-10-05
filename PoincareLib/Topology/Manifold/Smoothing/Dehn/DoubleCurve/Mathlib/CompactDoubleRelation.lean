import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness of the actual distinct-point fiber relation

For a continuous locally injective map from a compact source, the
diagonal is open inside the compact fiber product. Its complement
therefore gives the compact set of distinct source pairs with the
same image. See Dehn028, section1, preparing Hatcher p.46.
-/

set_option autoImplicit false

open Set

/-- Local injectivity makes the distinct-point relation compact
inside the actual fiber product. This does not use closedness of
the complement of the diagonal in the whole product.
See Dehn028, section1. -/
theorem IsLocallyInjective.isCompact_doubleRelation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}
    (hf : IsLocallyInjective f) (hc : Continuous f) :
    IsCompact {z : X × X | f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  have hT : IsCompact {z : X × X | f z.1 = f z.2} :=
    (isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)).isCompact
  let : CompactSpace (f.Pullback f) := isCompact_iff_compactSpace.mp hT
  have hD : IsCompact (f.pullbackDiagonal)ᶜ :=
    (isLocallyInjective_iff_isOpen_diagonal.mp hf).isClosed_compl.isCompact
  have himage : (Subtype.val : f.Pullback f → X × X) '' (f.pullbackDiagonal)ᶜ =
      {z : X × X | f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
    · rintro ⟨heq, hne⟩
      exact ⟨⟨z, heq⟩, hne, rfl⟩
  rw [← himage]
  exact hD.image continuous_subtype_val
