import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcRegionPullback

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem isOpen_end_region_of_avoiding_other_end
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed B) (hcover : A ∪ B = univ)
    {O : Set A} (hO : IsOpen O) (hdis : Disjoint (Subtype.val '' O) B) :
    IsOpen (Subtype.val '' O) := by
  obtain ⟨V,hV,rfl⟩ := isOpen_induced_iff.mp hO
  have heq : Subtype.val '' (Subtype.val ⁻¹' V : Set A) = V ∩ Bᶜ := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,fun hb => disjoint_left.mp hdis (mem_image_of_mem Subtype.val hz) hb⟩
    · rintro ⟨hx,hb⟩
      have hxa : x ∈ A := (hcover.symm.subset (mem_univ x)).resolve_right hb
      exact ⟨⟨x,hxa⟩,hx,rfl⟩
  rw [heq]
  exact hV.inter hB.isOpen_compl

theorem end_region_in_whole_surface
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ)
    {O : Set A} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hsc : IsSimplyConnected O) (hdis : Disjoint (Subtype.val '' O) B) :
    IsOpen (Subtype.val '' O) ∧ IsCompact (closure (Subtype.val '' O)) ∧
      IsSimplyConnected (Subtype.val '' O) ∧
      closure (Subtype.val '' O) = Subtype.val '' closure O ∧
      frontier (Subtype.val '' O) = Subtype.val '' frontier O := by
  have hopen := isOpen_end_region_of_avoiding_other_end hB hcover hO hdis
  have hcl : closure (Subtype.val '' O) = Subtype.val '' closure O :=
    hA.isClosedEmbedding_subtypeVal.closure_image_eq O
  refine ⟨hopen,hcl ▸ hK.image continuous_subtype_val,
    Topology.IsEmbedding.subtypeVal.isSimplyConnected_image.mpr hsc,hcl,?_⟩
  rw [hopen.frontier_eq,hcl,hO.frontier_eq,Set.image_sdiff Subtype.val_injective]

theorem isOpen_image_of_embedding_into_range_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsEmbedding f) {O : Set X}
    (hO : IsOpen O) (hint : f '' O ⊆ interior (range f)) : IsOpen (f '' O) := by
  obtain ⟨V,hV,rfl⟩ := hf.isInducing.isOpen_iff.mp hO
  have heq : f '' (f ⁻¹' V) = V ∩ interior (range f) := by
    apply Subset.antisymm
    · exact fun _ hx => ⟨(image_preimage_subset f V) hx,hint hx⟩
    · rintro y ⟨hy,hyr⟩
      obtain ⟨x,rfl⟩ := interior_subset hyr
      exact ⟨x,hy,rfl⟩
  rw [heq]
  exact hV.inter isOpen_interior

theorem region_image_in_range_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) {O : Set X}
    (hO : IsOpen O) (hK : IsCompact (closure O)) (hsc : IsSimplyConnected O)
    (hint : f '' O ⊆ interior (range f)) :
    IsOpen (f '' O) ∧ IsCompact (closure (f '' O)) ∧ IsSimplyConnected (f '' O) ∧
      closure (f '' O) = f '' closure O ∧ frontier (f '' O) = f '' frontier O := by
  have hopen := isOpen_image_of_embedding_into_range_interior hf.isEmbedding hO hint
  have hcl := hf.closure_image_eq O
  refine ⟨hopen,hcl ▸ hK.image hf.continuous,
    hf.isEmbedding.isSimplyConnected_image.mpr hsc,hcl,?_⟩
  rw [hopen.frontier_eq,hcl,hO.frontier_eq,Set.image_sdiff hf.injective]

end PoincareConjecture.M76
