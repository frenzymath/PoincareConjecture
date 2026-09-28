import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Compactness.Compact










set_option autoImplicit false

open Set





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
