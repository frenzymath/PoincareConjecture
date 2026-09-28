import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionNested

set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]

theorem prod_singleton_one_subset_frontier_cylinder {U C : Set X} (hUC : U ⊆ C) :
    U ×ˢ {(1 : ℝ)} ⊆ frontier (C ×ˢ Icc (-1 : ℝ) 1) := by
  rw [frontier_prod_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have ht' : t = 1 := ht
  subst t
  exact Or.inl ⟨subset_closure (hUC hx), by simp⟩

theorem preimage_top_face_eq_preimage_positive_band {U C : Set X}
    (hUC : U ⊆ interior C) :
    (Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹' (U ×ˢ {1}) =
      (Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹' (U ×ˢ Ioi 0) := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, by rw [show (x : X × ℝ).2 = 1 from hx.2]; norm_num⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hfront : (x : X × ℝ) ∈
        (closure C ×ˢ {(-1 : ℝ), 1}) ∪ (frontier C ×ˢ closure (Icc (-1 : ℝ) 1)) := by
      simpa only [frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)] using
        (frontier_prod_eq C (Icc (-1 : ℝ) 1)).subset x.property
    rcases hfront with htop | hside
    · have ht : (x : X × ℝ).2 = -1 ∨ (x : X × ℝ).2 = 1 := by
        simpa only [mem_insert_iff, mem_singleton_iff] using htop.2
      rcases ht with ht | ht
      · have hpos : 0 < (x : X × ℝ).2 := hx.2
        rw [ht] at hpos
        norm_num at hpos
      · exact ht
    · exact (hside.1.2 (hUC hx.1)).elim

theorem isOpen_preimage_top_face {U C : Set X} (hU : IsOpen U)
    (hUC : U ⊆ interior C) :
    IsOpen ((Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
      (U ×ˢ {1})) := by
  rw [preimage_top_face_eq_preimage_positive_band hUC]
  exact (hU.prod isOpen_Ioi).preimage continuous_subtype_val

theorem closure_preimage_top_face {U C : Set X} (hUC : U ⊆ C) :
    closure ((Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
      (U ×ˢ {1})) =
      (Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
        (closure U ×ˢ {1}) := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    image_preimage_eq_of_subset (by
      simpa using prod_singleton_one_subset_frontier_cylinder hUC),
    closure_prod_eq, isClosed_singleton.closure_eq]

theorem frontier_preimage_top_face {U C : Set X} (hU : IsOpen U)
    (hUC : U ⊆ interior C) :
    frontier ((Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
      (U ×ˢ {1})) =
      (Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
        (frontier U ×ˢ {1}) := by
  change closure ((Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
      (U ×ˢ {1})) \
      interior ((Subtype.val : frontier (C ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
        (U ×ˢ {1})) = _
  rw [closure_preimage_top_face (hUC.trans interior_subset),
    (isOpen_preimage_top_face hU hUC).interior_eq, ← preimage_sdiff]
  congr 1
  rw [frontier, hU.interior_eq]
  ext p
  simp only [mem_sdiff, mem_prod]
  tauto

theorem isCompact_cylinderExterior [T2Space X] {U C : Set X}
    (hC : IsCompact C) (hU : IsOpen U) (hUC : U ⊆ interior C) :
    IsCompact (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) := by
  have heq : frontier (C ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1} =
      frontier (C ×ˢ Icc (-1 : ℝ) 1) ∩ (U ×ˢ Ioi (0 : ℝ))ᶜ := by
    ext x
    by_cases hx : x ∈ frontier (C ×ˢ Icc (-1 : ℝ) 1)
    · have hmem := Set.ext_iff.mp (preimage_top_face_eq_preimage_positive_band hUC)
        ⟨x, hx⟩
      change (x ∈ frontier (C ×ˢ Icc (-1 : ℝ) 1) ∧ x ∉ U ×ˢ {1}) ↔
        (x ∈ frontier (C ×ˢ Icc (-1 : ℝ) 1) ∧ x ∉ U ×ˢ Ioi (0 : ℝ))
      exact and_congr_right fun _ => not_congr hmem
    · simp only [mem_sdiff, mem_inter_iff, hx, false_and]
  rw [heq]
  have hfront : IsCompact (frontier (C ×ˢ Icc (-1 : ℝ) 1)) :=
    (hC.prod isCompact_Icc).of_isClosed_subset isClosed_frontier
      (hC.isClosed.prod isClosed_Icc).frontier_subset
  exact hfront.inter_right (hU.prod isOpen_Ioi).isClosed_compl

theorem alexander_nested_region_inter_cylinderExterior {U V C b c d q : Set X}
    (hV : IsOpen V) (hUV : U ⊆ V) (hUC : closure U ⊆ C)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hbc : b ∩ c = q) (hqd : q ⊆ d) :
    (closure U ×ˢ {(1 : ℝ)}) ∩
        (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) = d ×ˢ {1} := by
  have hinter := alexander_nested_region_inter_exterior hV hUV hUf hVf hbc hqd
  have htop := prod_singleton_one_subset_frontier_cylinder hUC
  ext x
  constructor
  · intro hx
    refine ⟨hinter.subset ⟨hx.1.1, ?_⟩, hx.1.2⟩
    intro hxV
    exact hx.2.2 ⟨hxV, hx.1.2⟩
  · intro hx
    have hxU := hinter.symm.subset hx.1
    refine ⟨⟨hxU.1, hx.2⟩, htop ⟨hxU.1, hx.2⟩, ?_⟩
    exact fun hxV => hxU.2 hxV.1

end Set
