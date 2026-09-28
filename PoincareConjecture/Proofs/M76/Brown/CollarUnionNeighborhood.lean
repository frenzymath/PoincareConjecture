import PoincareConjecture.Proofs.M76.Brown.AmbientSideCollars
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set

namespace BrownCollar.AmbientSideCollars

variable {X : Type*} [TopologicalSpace X] {S : Set X} (C : AmbientSideCollars S)

def positiveImage : Set X := (Subtype.val : C.positive → X) '' C.positive_range

def negativeImage : Set X := (Subtype.val : C.negative → X) '' C.negative_range

def collarUnion : Set X := C.positiveImage ∪ C.negativeImage

theorem positive_subset_neighborhood : C.positive ⊆ C.neighborhood := by
  rw [← C.union_eq]
  exact subset_union_left

theorem negative_subset_neighborhood : C.negative ⊆ C.neighborhood := by
  rw [← C.union_eq]
  exact subset_union_right

theorem positiveImage_subset : C.positiveImage ⊆ C.positive := by
  rintro _ ⟨p, _, rfl⟩
  exact p.property

theorem negativeImage_subset : C.negativeImage ⊆ C.negative := by
  rintro _ ⟨p, _, rfl⟩
  exact p.property

theorem mem_positiveImage (p : C.positive) :
    (p : X) ∈ C.positiveImage ↔ p ∈ C.positive_range := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp : q = p := Subtype.ext heq
    simpa only [hqp] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem mem_negativeImage (p : C.negative) :
    (p : X) ∈ C.negativeImage ↔ p ∈ C.negative_range := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp : q = p := Subtype.ext heq
    simpa only [hqp] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem base_subset_positiveImage : S ⊆ C.positiveImage := by
  intro x hx
  let b : S := ⟨x, hx⟩
  exact ⟨(C.positive_collar (collarBase b) : C.positive),
    (C.positive_collar (collarBase b)).property, C.positive_base b⟩

theorem base_subset_negativeImage : S ⊆ C.negativeImage := by
  intro x hx
  let b : S := ⟨x, hx⟩
  exact ⟨(C.negative_collar (collarBase b) : C.negative),
    (C.negative_collar (collarBase b)).property, C.negative_base b⟩

theorem images_inter : C.positiveImage ∩ C.negativeImage = S := by
  apply Subset.antisymm
  · intro x hx
    rw [← C.inter_eq]
    exact ⟨C.positiveImage_subset hx.1, C.negativeImage_subset hx.2⟩
  · exact subset_inter C.base_subset_positiveImage C.base_subset_negativeImage

theorem collarUnion_subset_neighborhood : C.collarUnion ⊆ C.neighborhood :=
  union_subset (C.positiveImage_subset.trans C.positive_subset_neighborhood)
    (C.negativeImage_subset.trans C.negative_subset_neighborhood)

theorem collarUnion_inter_positive : C.collarUnion ∩ C.positive = C.positiveImage := by
  apply Subset.antisymm
  · rintro x ⟨hp | hm, hx⟩
    · exact hp
    · apply C.base_subset_positiveImage
      rw [← C.inter_eq]
      exact ⟨hx, C.negativeImage_subset hm⟩
  · exact subset_inter subset_union_left C.positiveImage_subset

theorem collarUnion_inter_negative : C.collarUnion ∩ C.negative = C.negativeImage := by
  apply Subset.antisymm
  · rintro x ⟨hp | hm, hx⟩
    · apply C.base_subset_negativeImage
      rw [← C.inter_eq]
      exact ⟨C.positiveImage_subset hp, hx⟩
    · exact hm
  · exact subset_inter subset_union_right C.negativeImage_subset




theorem isOpen_collarUnion : IsOpen C.collarUnion := by
  let ip := Set.inclusion C.positive_subset_neighborhood
  let im := Set.inclusion C.negative_subset_neighborhood
  have hpclosed : IsClosed (ip '' C.positive_rangeᶜ) :=
    (Topology.IsClosedEmbedding.inclusion C.positive_subset_neighborhood
      C.positive_closed).isClosedMap _ C.positive_open.isClosed_compl
  have hmclosed : IsClosed (im '' C.negative_rangeᶜ) :=
    (Topology.IsClosedEmbedding.inclusion C.negative_subset_neighborhood
      C.negative_closed).isClosedMap _ C.negative_open.isClosed_compl
  have heq : ((Subtype.val : C.neighborhood → X) ⁻¹' C.collarUnion)ᶜ =
      ip '' C.positive_rangeᶜ ∪ im '' C.negative_rangeᶜ := by
    ext y
    constructor
    · intro hy
      have hyu : (y : X) ∈ C.positive ∪ C.negative := by
        rw [C.union_eq]
        exact y.property
      rcases hyu with hyp | hym
      · refine Or.inl ⟨⟨y.val, hyp⟩, ?_, Subtype.ext rfl⟩
        intro h
        exact hy (Or.inl ⟨⟨y.val, hyp⟩, h, rfl⟩)
      · refine Or.inr ⟨⟨y.val, hym⟩, ?_, Subtype.ext rfl⟩
        intro h
        exact hy (Or.inr ⟨⟨y.val, hym⟩, h, rfl⟩)
    · rintro (hy | hy)
      · rcases hy with ⟨p, hp, rfl⟩
        intro h
        have himage : (p : X) ∈ C.positiveImage := by
          rw [← C.collarUnion_inter_positive]
          exact ⟨h, p.property⟩
        exact hp ((C.mem_positiveImage p).mp himage)
      · rcases hy with ⟨p, hp, rfl⟩
        intro h
        have himage : (p : X) ∈ C.negativeImage := by
          rw [← C.collarUnion_inter_negative]
          exact ⟨h, p.property⟩
        exact hp ((C.mem_negativeImage p).mp himage)
  have hopen : IsOpen ((Subtype.val : C.neighborhood → X) ⁻¹' C.collarUnion) := by
    apply isClosed_compl_iff.mp
    rw [heq]
    exact hpclosed.union hmclosed
  have himage := C.open_neighborhood.isOpenMap_subtype_val _ hopen
  rw [Subtype.image_preimage_coe,
    inter_eq_right.mpr C.collarUnion_subset_neighborhood] at himage
  exact himage

theorem positiveImage_closed :
    IsClosed ((Subtype.val : C.collarUnion → X) ⁻¹' C.positiveImage) := by
  have heq : (Subtype.val : C.collarUnion → X) ⁻¹' C.positiveImage =
      (Subtype.val : C.collarUnion → X) ⁻¹' C.positive := by
    ext x
    constructor
    · intro hx
      exact C.positiveImage_subset hx
    · intro hx
      rw [mem_preimage, ← C.collarUnion_inter_positive]
      exact ⟨x.property, hx⟩
  rw [heq]
  exact C.positive_closed.preimage (continuous_inclusion C.collarUnion_subset_neighborhood)

theorem negativeImage_closed :
    IsClosed ((Subtype.val : C.collarUnion → X) ⁻¹' C.negativeImage) := by
  have heq : (Subtype.val : C.collarUnion → X) ⁻¹' C.negativeImage =
      (Subtype.val : C.collarUnion → X) ⁻¹' C.negative := by
    ext x
    constructor
    · intro hx
      exact C.negativeImage_subset hx
    · intro hx
      rw [mem_preimage, ← C.collarUnion_inter_negative]
      exact ⟨x.property, hx⟩
  rw [heq]
  exact C.negative_closed.preimage (continuous_inclusion C.collarUnion_subset_neighborhood)

noncomputable def positiveImageHomeomorph :
    (S × Ico (0 : ℝ) 1) ≃ₜ C.positiveImage :=
  C.positive_collar.trans (Topology.IsEmbedding.subtypeVal.homeomorphImage C.positive_range)

noncomputable def negativeImageHomeomorph :
    (S × Ico (0 : ℝ) 1) ≃ₜ C.negativeImage :=
  C.negative_collar.trans (Topology.IsEmbedding.subtypeVal.homeomorphImage C.negative_range)

noncomputable def positiveUnionMap : S × Ico (0 : ℝ) 1 → C.collarUnion :=
  Set.inclusion subset_union_left ∘ C.positiveImageHomeomorph

noncomputable def negativeUnionMap : S × Ico (0 : ℝ) 1 → C.collarUnion :=
  Set.inclusion subset_union_right ∘ C.negativeImageHomeomorph

theorem positiveUnionMap_base (s : S) :
    (C.positiveUnionMap (collarBase s) : X) = (s : X) := C.positive_base s

theorem negativeUnionMap_base (s : S) :
    (C.negativeUnionMap (collarBase s) : X) = (s : X) := C.negative_base s

theorem isClosedEmbedding_positiveUnionMap : Topology.IsClosedEmbedding C.positiveUnionMap :=
  (Topology.IsClosedEmbedding.inclusion subset_union_left C.positiveImage_closed).comp
    C.positiveImageHomeomorph.isClosedEmbedding

theorem isClosedEmbedding_negativeUnionMap : Topology.IsClosedEmbedding C.negativeUnionMap :=
  (Topology.IsClosedEmbedding.inclusion subset_union_right C.negativeImage_closed).comp
    C.negativeImageHomeomorph.isClosedEmbedding

end BrownCollar.AmbientSideCollars
