import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.BoundaryGraphAttachment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalPrimalSectors

set_option autoImplicit false

open Set Geometry Classical

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {d q : Set E} {marks : Fin 4 → E}

namespace OriginalPrimalSectorDecomposition

variable (C : OriginalPrimalSectorDecomposition d q marks)

theorem sector_subset (i : Fin 4) : C.sector i ⊆ d := by
  intro x hx
  apply C.sector_cover.subset
  fin_cases i
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr hx)
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)

theorem rim_subset (i : Fin 4) : C.rim i ⊆ q :=
  (C.sector_rim i).symm.subset.trans inter_subset_right

theorem center_mem_spoke (i : Fin 4) : C.center ∈ C.spoke i :=
  (C.spoke_ball i).1 (Or.inl rfl)

theorem spoke_subset_sector (i : Fin 4) : C.spoke i ⊆ C.sector i :=
  (subset_union_left.trans subset_union_right).trans (C.sector_ball i).1

theorem center_mem_sector (i : Fin 4) : C.center ∈ C.sector i :=
  C.spoke_subset_sector i (C.center_mem_spoke i)

theorem spoke_eq_sector_inter (i : Fin 4) :
    C.spoke i = C.sector (i + 3) ∩ C.sector i := by
  have hi : i + 3 + 1 = i := by fin_cases i <;> decide
  simpa only [hi] using (C.sector_inter_next (i + 3)).symm

theorem spoke_sector_mem_iff (i j : Fin 4) {x : E}
    (hx : x ∈ C.spoke i) (hxc : x ≠ C.center) :
    x ∈ C.sector j ↔ j = i ∨ j = i + 3 := by
  have hpair := (C.spoke_eq_sector_inter i).subset hx
  constructor
  · intro hxj
    by_contra hne
    have hj : j = i + 1 ∨ j = i + 2 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hj with rfl | rfl
    · have hi : i + 3 + 2 = i + 1 := by fin_cases i <;> decide
      have hc := (C.sector_inter_opposite (i + 3)).subset ⟨hpair.1, hi.symm ▸ hxj⟩
      exact hxc hc
    · exact hxc ((C.sector_inter_opposite i).subset ⟨hpair.2, hxj⟩)
  · rintro (rfl | rfl)
    · exact hpair.2
    · exact hpair.1

theorem sector_inter_subset_spokes (i j : Fin 4) (hij : i ≠ j) :
    C.sector i ∩ C.sector j ⊆ ⋃ k, C.spoke k := by
  rintro x ⟨hxi, hxj⟩
  have hj : j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hj with rfl | rfl | rfl
  · exact mem_iUnion.mpr ⟨i + 1, (C.sector_inter_next i).subset ⟨hxi, hxj⟩⟩
  · have hxc : x = C.center := (C.sector_inter_opposite i).subset ⟨hxi, hxj⟩
    exact mem_iUnion.mpr ⟨0, hxc.symm ▸ C.center_mem_spoke 0⟩
  · exact mem_iUnion.mpr ⟨i, (C.spoke_eq_sector_inter i).symm.subset ⟨hxj, hxi⟩⟩

theorem existsUnique_sector_of_not_mem_spokes {x : E} (hx : x ∈ d)
    (hsp : x ∉ ⋃ k, C.spoke k) : ∃! i, x ∈ C.sector i := by
  have hex : ∃ i, x ∈ C.sector i := by
    rcases C.sector_cover.symm.subset hx with (h | h) | (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra hji
  exact hsp (C.sector_inter_subset_spokes j i hji ⟨hj, hi⟩)

section Attachment

variable (g : Fin 4 → E → F) (k : Fin 4 → (E × F) → ℝ) (s : Set (E × F))

theorem attached_fiber_outside_primal {x : E} (hx : x ∉ d) :
    graphAttachmentCarrier g k s C.sector ∩
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {x} =
      zeroSheet '' (s ∩ Prod.fst ⁻¹' {x}) := by
  rw [graphAttachment_projection_fiber]
  have hi : ∀ i, x ∉ C.sector i := fun i h ↦ hx (C.sector_subset i h)
  simp only [if_neg (hi _), iUnion_empty, union_empty]

theorem attached_primal_fiber
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hbase : Prod.fst '' s ∩ d ⊆ q)
    (hgap : s ∩ Prod.fst ⁻¹' q = ⋃ i, heightGraph (g i) '' C.rim i)
    {x : E} (hx : x ∈ d) :
    graphAttachmentCarrier g k s C.sector ∩
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {x} =
      ⋃ i, if x ∈ C.sector i then {graphAttachmentSheet g k i x} else ∅ := by
  rw [graphAttachment_projection_fiber]
  apply union_eq_right.mpr
  rintro p ⟨y, ⟨hy, hyx⟩, rfl⟩
  have hyx' : y.1 = x := hyx
  have hxq := hbase ⟨⟨y, hy, hyx'⟩, hx⟩
  have hygap : y ∈ s ∩ Prod.fst ⁻¹' q :=
    ⟨hy, show y.1 ∈ q from hyx'.symm ▸ hxq⟩
  rw [hgap] at hygap
  obtain ⟨i, v, hv, hvy⟩ := mem_iUnion.mp hygap
  have hvx : v = x := (congrArg Prod.fst hvy).trans hyx'
  subst v
  have hxi : x ∈ C.sector i := (C.sector_rim i).symm.subset hv |>.1
  have heq : graphAttachmentSheet g k i x = zeroSheet y :=
    (separatedSheet_eq_zeroSheet_iff k i _ _).mpr ⟨hvy, (hz i x hxi).mpr hv⟩
  exact mem_iUnion.mpr ⟨i, by rw [if_pos hxi]; exact heq.symm⟩

theorem attached_sector_copies_ne
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' C.rim i)
      (heightGraph (g j) '' C.rim j)))
    {i j : Fin 4} (hij : i ≠ j) {x : E}
    (hi : x ∈ C.sector i) (hj : x ∈ C.sector j) :
    graphAttachmentSheet g k i x ≠ graphAttachmentSheet g k j x := by
  intro heq
  obtain ⟨heq', hi0, hj0⟩ := (separatedSheet_distinct_eq_iff k hij _ _).mp heq
  exact Set.disjoint_left.mp (hdis hij)
    (mem_image_of_mem (heightGraph (g i)) ((hz i x hi).mp hi0))
    (heq'.symm ▸ mem_image_of_mem (heightGraph (g j)) ((hz j x hj).mp hj0))

theorem attached_center_fiber
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hbase : Prod.fst '' s ∩ d ⊆ q)
    (hgap : s ∩ Prod.fst ⁻¹' q = ⋃ i, heightGraph (g i) '' C.rim i) :
    graphAttachmentCarrier g k s C.sector ∩
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {C.center} =
      range (fun i ↦ graphAttachmentSheet g k i C.center) := by
  rw [C.attached_primal_fiber g k s hz hbase hgap C.center_mem.1]
  simp only [if_pos (C.center_mem_sector _), iUnion_singleton_eq_range]

theorem attached_center_fiber_ncard
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hbase : Prod.fst '' s ∩ d ⊆ q)
    (hgap : s ∩ Prod.fst ⁻¹' q = ⋃ i, heightGraph (g i) '' C.rim i)
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' C.rim i)
      (heightGraph (g j) '' C.rim j))) :
    (graphAttachmentCarrier g k s C.sector ∩
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {C.center}).ncard = 4 := by
  rw [C.attached_center_fiber g k s hz hbase hgap]
  have hinj : Function.Injective (fun i ↦ graphAttachmentSheet g k i C.center) := by
    intro i j heq
    by_contra hij
    exact C.attached_sector_copies_ne g k hz hdis hij
      (C.center_mem_sector i) (C.center_mem_sector j) heq
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using ncard_range_of_injective hinj

theorem attached_spoke_fiber
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hbase : Prod.fst '' s ∩ d ⊆ q)
    (hgap : s ∩ Prod.fst ⁻¹' q = ⋃ i, heightGraph (g i) '' C.rim i)
    (i : Fin 4) {x : E} (hx : x ∈ C.spoke i) (hxc : x ≠ C.center) :
    graphAttachmentCarrier g k s C.sector ∩
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {x} =
      {graphAttachmentSheet g k i x, graphAttachmentSheet g k (i + 3) x} := by
  rw [C.attached_primal_fiber g k s hz hbase hgap (C.spoke_subset i hx)]
  ext p
  constructor
  · intro hp
    obtain ⟨j, hp⟩ := mem_iUnion.mp hp
    split_ifs at hp with hxj
    · rcases (C.spoke_sector_mem_iff i j hx hxc).mp hxj with rfl | rfl
      · exact Or.inl hp
      · exact Or.inr hp
    · exact hp.elim
  · rintro (hp | hp)
    · exact mem_iUnion.mpr ⟨i, by rw [if_pos (C.spoke_subset_sector i hx)]; exact hp⟩
    · exact mem_iUnion.mpr ⟨i + 3, by
        rw [if_pos ((C.spoke_eq_sector_inter i).subset hx).1]; exact hp⟩

theorem attached_spoke_fiber_ncard
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hbase : Prod.fst '' s ∩ d ⊆ q)
    (hgap : s ∩ Prod.fst ⁻¹' q = ⋃ i, heightGraph (g i) '' C.rim i)
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' C.rim i)
      (heightGraph (g j) '' C.rim j)))
    (i : Fin 4) {x : E} (hx : x ∈ C.spoke i) (hxc : x ≠ C.center) :
    (graphAttachmentCarrier g k s C.sector ∩
      (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {x}).ncard = 2 := by
  rw [C.attached_spoke_fiber g k s hz hbase hgap i hx hxc]
  have hi : i ≠ i + 3 := by fin_cases i <;> decide
  exact Set.ncard_pair (C.attached_sector_copies_ne g k hz hdis hi
    (C.spoke_subset_sector i hx) ((C.spoke_eq_sector_inter i).subset hx).1)

theorem attached_spoke_traces_subset_rim
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' C.rim i)
      (heightGraph (g j) '' C.rim j))) (b : Set (E × F)) (i : Fin 4) :
    graphAttachmentSheet g k i '' (C.spoke i ∪ C.spoke (i + 1)) ⊆
      graphAttachmentRim g k b (fun j ↦ C.rim j ∪ (C.spoke j ∪ C.spoke (j + 1)))
        C.rim (fun j ↦ marks (C.order j)) (fun j ↦ marks (C.order (j + 1))) := by
  rintro p ⟨x, hx, rfl⟩
  apply (graphAttachmentSheet_mem_rim_iff g k (fun j ↦ (C.sector_ball j).1)
    hz hdis i (Or.inr hx)).mpr
  intro hxr
  have hxq := C.rim_subset i hxr
  rcases hx with hxi | hxi
  · exact Or.inl ((C.spoke_rim i).subset ⟨hxi, hxq⟩)
  · exact Or.inr ((C.spoke_rim (i + 1)).subset ⟨hxi, hxq⟩)

theorem attached_centers_mem_rim
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' C.rim i)
      (heightGraph (g j) '' C.rim j))) (b : Set (E × F)) (i : Fin 4) :
    graphAttachmentSheet g k i C.center ∈
      graphAttachmentRim g k b (fun j ↦ C.rim j ∪ (C.spoke j ∪ C.spoke (j + 1)))
        C.rim (fun j ↦ marks (C.order j)) (fun j ↦ marks (C.order (j + 1))) :=
  C.attached_spoke_traces_subset_rim g k hz hdis b i
    (mem_image_of_mem _ (Or.inl (C.center_mem_spoke i)))

theorem attached_singleton_fiber_off_spokes
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hbase : Prod.fst '' s ∩ d ⊆ q)
    (hgap : s ∩ Prod.fst ⁻¹' q = ⋃ i, heightGraph (g i) '' C.rim i)
    {x : E} (hx : x ∈ d) (hsp : x ∉ ⋃ i, C.spoke i) :
    ∃ i : Fin 4,
      graphAttachmentCarrier g k s C.sector ∩
        (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) ⁻¹' {x} =
        {graphAttachmentSheet g k i x} := by
  obtain ⟨i, hi, huniq⟩ := C.existsUnique_sector_of_not_mem_spokes hx hsp
  refine ⟨i, ?_⟩
  rw [C.attached_primal_fiber g k s hz hbase hgap hx]
  ext p
  constructor
  · intro hp
    obtain ⟨j, hp⟩ := mem_iUnion.mp hp
    split_ifs at hp with hj
    · simpa only [huniq j hj] using hp
    · exact hp.elim
  · intro hp
    exact mem_iUnion.mpr ⟨i, by rw [if_pos hi]; exact hp⟩

end Attachment
end OriginalPrimalSectorDecomposition
end PoincareConjecture.M76.OriginalTriangleCopies
