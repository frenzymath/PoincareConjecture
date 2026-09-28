import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.RetainedModelNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NestedCollarCut









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

private theorem closure_model_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Q E : Set X} {K : Set Y} (H : Q ≃ₜ K) (f : X → Y)
    (hH : ∀ x : Q, (H x : Y) = f x) (hK : IsClosed K) (hEQ : E ⊆ Q) :
    closure (f '' E) = f '' (Q ∩ closure E) := by
  let g : Q → Y := fun x => H x
  have hg : Topology.IsClosedEmbedding g :=
    hK.isClosedEmbedding_subtypeVal.comp H.isClosedEmbedding
  have himage (A : Set X) : g '' ((Subtype.val : Q → X) ⁻¹' A) = f '' (Q ∩ A) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨x.property, hx⟩, (hH x).symm⟩
    · rintro ⟨x, ⟨hxQ, hxA⟩, rfl⟩
      exact ⟨⟨x, hxQ⟩, hxA, hH ⟨x, hxQ⟩⟩
  have hc := hg.closure_image_eq ((Subtype.val : Q → X) ⁻¹' E)
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_coe, inter_eq_right.mpr hEQ] at hc
  simpa only [himage, inter_eq_right.mpr hEQ] using hc




theorem nested_cap_relative_frontier
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    {R P O : Set X} {K C : Set Y}
    (hR : IsCompact R) (hRP : R ⊆ interior P)
    (hO : IsOpen O) (hOR : closure O ⊆ interior R)
    (H : (P \ O : Set X) ≃ₜ K) (f : X → Y)
    (hH : ∀ x : (P \ O : Set X), (H x : Y) = f x)
    (hK : IsClosed K) (hC : IsClosed C)
    (hattach : C ∩ K ⊆ f '' (interior R \ O)) :
    frontier ((Subtype.val : (K ∪ C : Set Y) → Y) ⁻¹' (f '' (R \ O) ∪ C)) =
      (Subtype.val : (K ∪ C : Set Y) → Y) ⁻¹' (f '' frontier R) ∧
    (IsCompact C → IsCompact (f '' (R \ O) ∪ C)) := by
  have hRQ : R \ O ⊆ P \ O := fun _ hx => ⟨interior_subset (hRP hx.1), hx.2⟩
  have hEQ : P \ R ⊆ P \ O := by
    intro x hx
    exact ⟨hx.1, fun hxO => hx.2 (interior_subset (hOR (subset_closure hxO)))⟩
  have hFi : InjOn f (P \ O) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))))
  have hF : ContinuousOn f (P \ O) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp H.continuous).congr (fun x => hH x)
  have hAcompact : IsCompact (f '' (R \ O)) :=
    (hR.diff hO).image_of_continuousOn (hF.mono hRQ)
  have hDclosed : IsClosed (f '' (R \ O) ∪ C) := hAcompact.isClosed.union hC
  have himageK : f '' (P \ O) = K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hH ⟨x, hx⟩ ▸ (H ⟨x, hx⟩).property
    · intro hy
      exact ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property,
        (hH (H.symm ⟨y, hy⟩)).symm.trans
          (congrArg Subtype.val (H.apply_symm_apply ⟨y, hy⟩))⟩
  have hnotInterior {x : X} (hx : x ∈ closure (P \ R)) : x ∉ interior R := by
    have hh : x ∈ closure Rᶜ := closure_mono (fun _ h => h.2) hx
    simpa only [closure_compl, mem_compl_iff] using hh
  have hfront {x : X} : x ∈ frontier R ↔ x ∈ R ∧ x ∈ closure (P \ R) := by
    constructor
    · intro hx
      have hxR := hR.isClosed.frontier_subset hx
      refine ⟨hxR, mem_closure_iff.mpr ?_⟩
      intro V hV hxV
      have hxcomp : x ∈ closure Rᶜ := by
        simpa only [closure_compl, mem_compl_iff] using hx.2
      obtain ⟨y, hyV, hyR⟩ := mem_closure_iff.mp hxcomp
        (V ∩ interior P) (hV.inter isOpen_interior) ⟨hxV, hRP hxR⟩
      exact ⟨y, hyV.1, interior_subset hyV.2, hyR⟩
    · rintro ⟨hxR, hxcl⟩
      rw [hR.isClosed.frontier_eq]
      exact ⟨hxR, hnotInterior hxcl⟩
  have hfrontQ : frontier R ⊆ R \ O := by
    intro x hx
    exact ⟨hR.isClosed.frontier_subset hx,
      fun hxO => hx.2 (hOR (subset_closure hxO))⟩
  have hcomplement : (K ∪ C) \ (f '' (R \ O) ∪ C) = f '' (P \ R) := by
    ext y
    constructor
    · rintro ⟨hyK | hyC, hyD⟩
      · obtain ⟨x, hx, rfl⟩ := himageK.symm.subset hyK
        exact ⟨x, ⟨hx.1, fun hxR => hyD (Or.inl ⟨x, ⟨hxR, hx.2⟩, rfl⟩)⟩, rfl⟩
      · exact False.elim (hyD (Or.inr hyC))
    · rintro ⟨x, hx, rfl⟩
      have hxQ := hEQ hx
      have hxK := himageK.subset (mem_image_of_mem f hxQ)
      refine ⟨Or.inl hxK, ?_⟩
      rintro (⟨z, hz, hzEq⟩ | hxC)
      · exact hx.2 ((hFi (hRQ hz) hxQ hzEq) ▸ hz.1)
      · obtain ⟨z, hz, hzEq⟩ := hattach ⟨hxC, hxK⟩
        have hzQ : z ∈ P \ O := ⟨interior_subset (hRP (interior_subset hz.1)), hz.2⟩
        exact hx.2 ((hFi hzQ hxQ hzEq) ▸ interior_subset hz.1)
  have hclosure := closure_model_image H f hH hK hEQ
  have hboundary : (f '' (R \ O) ∪ C) ∩ closure (f '' (P \ R)) = f '' frontier R := by
    rw [hclosure]
    ext y
    constructor
    · rintro ⟨hyD, x, ⟨hxQ, hxcl⟩, rfl⟩
      have hxK := himageK.subset (mem_image_of_mem f hxQ)
      rcases hyD with ⟨z, hz, hzEq⟩ | hxC
      · have hxR : x ∈ R := (hFi (hRQ hz) hxQ hzEq) ▸ hz.1
        exact ⟨x, hfront.mpr ⟨hxR, hxcl⟩, rfl⟩
      · obtain ⟨z, hz, hzEq⟩ := hattach ⟨hxC, hxK⟩
        have hzQ : z ∈ P \ O := ⟨interior_subset (hRP (interior_subset hz.1)), hz.2⟩
        exact False.elim (hnotInterior hxcl ((hFi hzQ hxQ hzEq) ▸ hz.1))
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Or.inl ⟨x, hfrontQ hx, rfl⟩,
        ⟨x, ⟨hRQ (hfrontQ hx), (hfront.mp hx).2⟩, rfl⟩⟩
  refine ⟨?_, fun hc => hAcompact.union hc⟩
  have hcomplImage : (Subtype.val : (K ∪ C : Set Y) → Y) ''
      ((Subtype.val : (K ∪ C : Set Y) → Y) ⁻¹' (f '' (R \ O) ∪ C))ᶜ =
      (K ∪ C) \ (f '' (R \ O) ∪ C) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hn⟩
      exact ⟨⟨y, hy⟩, hn, rfl⟩
  rw [frontier_eq_closure_inter_closure,
    (hDclosed.preimage continuous_subtype_val).closure_eq,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    hcomplImage, hcomplement, ← preimage_inter, hboundary]




theorem nested_cap_relative_frontier_off_closed
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    {R P O : Set X} {K C Z : Set Y}
    (hR : IsCompact R) (hRP : R ⊆ interior P)
    (hO : IsOpen O) (hOR : closure O ⊆ interior R)
    (H : (P \ O : Set X) ≃ₜ K) (f : X → Y)
    (hH : ∀ x : (P \ O : Set X), (H x : Y) = f x)
    (hK : IsClosed K) (hC : IsClosed C)
    (hattach : C ∩ K ⊆ f '' (interior R \ O))
    (hZ : IsClosed Z) (hDZ : Disjoint (f '' (R \ O) ∪ C) Z) :
    frontier ((Subtype.val : ((K ∪ C) \ Z : Set Y) → Y) ⁻¹' (f '' (R \ O) ∪ C)) =
      (Subtype.val : ((K ∪ C) \ Z : Set Y) → Y) ⁻¹' (f '' frontier R) ∧
    (IsCompact C → IsCompact ((Subtype.val : ((K ∪ C) \ Z : Set Y) → Y) ⁻¹'
      (f '' (R \ O) ∪ C))) := by
  obtain ⟨hfront, hcompact⟩ := nested_cap_relative_frontier hR hRP hO hOR H f hH hK hC hattach
  have hopen : IsOpen ((Subtype.val : (K ∪ C : Set Y) → Y) ⁻¹' ((K ∪ C) \ Z)) := by
    convert hZ.isOpen_compl.preimage
      (continuous_subtype_val : Continuous (Subtype.val : (K ∪ C : Set Y) → Y)) using 1
    ext x
    exact and_iff_right x.property
  have hj := Topology.IsOpenEmbedding.inclusion
    (sdiff_subset : (K ∪ C) \ Z ⊆ K ∪ C) hopen
  refine ⟨?_, ?_⟩
  · have hh := hj.isOpenMap.preimage_frontier_eq_frontier_preimage hj.continuous
      ((Subtype.val : (K ∪ C : Set Y) → Y) ⁻¹' (f '' (R \ O) ∪ C))
    rw [hfront] at hh
    exact hh.symm
  · intro hc
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' (hcompact hc)
    rw [Subtype.range_coe]
    intro y hy
    refine ⟨?_, fun hz => disjoint_left.mp hDZ hy hz⟩
    rcases hy with ⟨x, hx, rfl⟩ | hy
    · have hxQ : x ∈ P \ O := ⟨interior_subset (hRP hx.1), hx.2⟩
      exact Or.inl (hH ⟨x, hxQ⟩ ▸ (H ⟨x, hxQ⟩).property)
    · exact Or.inr hy

end PoincareConjecture.M76
