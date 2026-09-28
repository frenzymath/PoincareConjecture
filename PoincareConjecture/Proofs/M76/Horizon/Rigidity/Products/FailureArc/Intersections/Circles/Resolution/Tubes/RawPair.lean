import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.PairCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

theorem nonempty_raw_crossing_of_disjoint_source_coordinates
    {E X ι : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
    {S₀ S₁ : Set E} {R : Set X} {x y : E}
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁) (hdis : Disjoint S₀ S₁)
    (hf : ContinuousOn f (S₀ ∪ S₁)) (hfi₀ : InjOn f S₀) (hfi₁ : InjOn f S₁)
    (hx : x ∈ S₀) (hy : y ∈ S₁) (hxy : f x = f y)
    (T : OpenPartialHomeomorph X (Fin 3 → ℝ)) (hxT : f x ∈ T.source)
    (hTR : T.source ⊆ interior R)
    (hcompat : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (hfirst : ∀ z ∈ T.source, z ∈ f '' S₀ ↔ T z 0 = 0)
    (hsecond : ∀ z ∈ T.source, z ∈ f '' S₁ ↔ T z 1 = 0) :
    Nonempty (RawSourceCrossing e f (S₀ ∪ S₁) R x y) := by
  let A := S₀ ∩ f ⁻¹' T.source
  let B := S₁ ∩ f ⁻¹' T.source
  have hopen₀ : IsOpen ((Subtype.val : (S₀ ∪ S₁ : Set E) → E) ⁻¹' S₀) := by
    have heq : (Subtype.val : (S₀ ∪ S₁ : Set E) → E) ⁻¹' S₀ =
        ((Subtype.val : (S₀ ∪ S₁ : Set E) → E) ⁻¹' S₁)ᶜ := by
      ext z
      constructor
      · exact fun hz hh => disjoint_left.mp hdis hz hh
      · exact fun hz => z.property.resolve_right hz
    rw [heq]
    exact (hS₁.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hopen₁ : IsOpen ((Subtype.val : (S₀ ∪ S₁ : Set E) → E) ⁻¹' S₁) := by
    have heq : (Subtype.val : (S₀ ∪ S₁ : Set E) → E) ⁻¹' S₁ =
        ((Subtype.val : (S₀ ∪ S₁ : Set E) → E) ⁻¹' S₀)ᶜ := by
      ext z
      constructor
      · exact fun hz hh => disjoint_left.mp hdis hh hz
      · exact fun hz => z.property.resolve_left hz
    rw [heq]
    exact (hS₀.isClosed.preimage continuous_subtype_val).isOpen_compl
  have hemb₀ : IsEmbedding (fun z : S₀ => f z) := by
    let : CompactSpace S₀ := isCompact_iff_compactSpace.mp hS₀
    exact ((hf.mono subset_union_left).domRestrict.isClosedEmbedding
      (fun z w h => Subtype.ext (hfi₀ z.property w.property h))).isEmbedding
  have hemb₁ : IsEmbedding (fun z : S₁ => f z) := by
    let : CompactSpace S₁ := isCompact_iff_compactSpace.mp hS₁
    exact ((hf.mono subset_union_right).domRestrict.isClosedEmbedding
      (fun z w h => Subtype.ext (hfi₁ z.property w.property h))).isEmbedding
  refine ⟨{
    chart := T, left := A, right := B,
    left_subset := fun _ hz => Or.inl hz.1,
    right_subset := fun _ hz => Or.inr hz.1,
    left_open := hopen₀.inter (T.open_source.preimage hf.domRestrict),
    right_open := hopen₁.inter (T.open_source.preimage hf.domRestrict),
    disjoint := hdis.mono inter_subset_left inter_subset_left,
    labels := Or.inl ⟨⟨hx,hxT⟩,⟨hy,show f y ∈ T.source from hxy ▸ hxT⟩⟩,
    point := hxT,
    left_embedding := hemb₀.comp (IsEmbedding.inclusion inter_subset_left),
    right_embedding := hemb₁.comp (IsEmbedding.inclusion inter_subset_left),
    whole_preimage := by ext z; exact or_and_right,
    compatible := hcompat,
    left_image := ?_, right_image := ?_, region := Or.inl hTR }⟩
  · intro z hz
    have hi : z ∈ f '' A ↔ z ∈ f '' S₀ := by
      constructor
      · exact fun h => image_mono inter_subset_left h
      · rintro ⟨a,ha,haz⟩
        exact ⟨a,⟨ha,show f a ∈ T.source from haz.symm ▸ hz⟩,haz⟩
    rw [hi,hfirst z hz]
    exact iff_self_and.mpr (fun _ => interior_subset (hTR hz))
  · intro z hz
    have hi : z ∈ f '' B ↔ z ∈ f '' S₁ := by
      constructor
      · exact fun h => image_mono inter_subset_left h
      · rintro ⟨a,ha,haz⟩
        exact ⟨a,⟨ha,show f a ∈ T.source from haz.symm ▸ hz⟩,haz⟩
    rw [hi,hsecond z hz]
    exact iff_self_and.mpr (fun _ => interior_subset (hTR hz))

theorem nonempty_raw_crossing_of_disjoint_source_pair
    {E X ι : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
    {S₀ S₁ : Set E} {R : Set X} {x y : E}
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁) (hdis : Disjoint S₀ S₁)
    (hf : ContinuousOn f (S₀ ∪ S₁)) (hfi₀ : InjOn f S₀) (hfi₁ : InjOn f S₁)
    (hx : x ∈ S₀) (hy : y ∈ S₁) (hxy : f x = f y) (hxR : f x ∈ interior R)
    (C : OriginalSurfacePairChart e (f '' S₀) (f '' S₁) (f x) false) :
    Nonempty (RawSourceCrossing e f (S₀ ∪ S₁) R x y) := by
  obtain ⟨T,hxT,hTR,hcompat,hfirst,hsecond⟩ :=
    exists_whole_pair_coordinates C (interior R) isOpen_interior hxR
  exact nonempty_raw_crossing_of_disjoint_source_coordinates hS₀ hS₁ hdis hf hfi₀ hfi₁
    hx hy hxy T hxT hTR hcompat hfirst hsecond

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
