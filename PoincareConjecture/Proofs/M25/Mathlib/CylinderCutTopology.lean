import PoincareConjecture.Proofs.M25.Mathlib.CofinalCylinderEscape

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

theorem cylinderCut_topology_of_not_isCompact
    {K W : Type*} [TopologicalSpace K] [TopologicalSpace W]
    [ConnectedSpace K] [CompactSpace K] [T2Space W]
    [WeaklyLocallyCompactSpace W]
    (e : OpenPartialHomeomorph (K × ℝ) W) {a b d : ℝ}
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hcompact : ∀ t ∈ Ioo a b, IsCompact (e.cylinderTail b t)ᶜ)
    (hnoncompact : ¬ IsCompact (univ : Set W)) (hd : d ∈ Ioo a b) :
    let lower := e.targetᶜ ∪ e '' (univ ×ˢ Ioo a d)
    IsOpen lower ∧ closure lower = (e.cylinderTail b d)ᶜ ∧
      interior (e.cylinderTail b d)ᶜ = lower ∧
      frontier lower = e.cylinderSlice d ∧
      frontier (e.cylinderTail b d)ᶜ = e.cylinderSlice d := by
  let lower := e.targetᶜ ∪ e '' (univ ×ˢ Ioo a d)
  change IsOpen lower ∧ closure lower = (e.cylinderTail b d)ᶜ ∧
    interior (e.cylinderTail b d)ᶜ = lower ∧
    frontier lower = e.cylinderSlice d ∧
    frontier (e.cylinderTail b d)ᶜ = e.cylinderSlice d
  have hescape : ∀ Q : Set W, IsCompact Q → ∀ t ∈ Ioo a b,
      ∃ s ∈ Ioo t b, Disjoint Q (e.cylinderTail b s) := by
    intro Q hQ t ht
    exact e.exists_cylinderTail_disjoint_compact_after_of_not_isCompact
      hsource hcompact hnoncompact hQ ht
  have hclosure := e.closure_cylinderTail_eq_union_slice_of_escape hsource hescape hd
  have hdom : univ ×ˢ Ioo a d ⊆ e.source := by
    rw [hsource]
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hd.2⟩
  have hnegative (x : W) : x ∈ e '' (univ ×ˢ Ioo a d) ↔
      x ∈ e.target ∧ (e.symm x).2 ∈ Ioo a d := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_source (hdom hz), ?_⟩
      rw [e.left_inv (hdom hz)]
      exact hz.2
    · rintro ⟨hx, hs⟩
      exact ⟨e.symm x, ⟨mem_univ _, hs⟩, e.right_inv hx⟩
  have hslice (x : W) : x ∈ e.cylinderSlice d ↔
      x ∈ e.target ∧ (e.symm x).2 = d := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzs : z ∈ e.source := by
        rw [hsource]
        exact ⟨hz.1, (mem_singleton_iff.mp hz.2).symm ▸ hd⟩
      refine ⟨e.map_source hzs, ?_⟩
      rw [e.left_inv hzs]
      exact hz.2
    · rintro ⟨hx, hs⟩
      exact ⟨e.symm x, ⟨mem_univ _, hs⟩, e.right_inv hx⟩
  have hdisjoint : Disjoint (e.cylinderTail b d) (e.cylinderSlice d) := by
    apply disjoint_left.mpr
    intro x hxT hxS
    have ht := ((e.mem_cylinderTail_iff hsource hd.1 x).mp hxT).2.1
    exact ht.ne' (hslice x |>.mp hxS).2
  have hinterior : interior (e.cylinderTail b d)ᶜ = lower := by
    rw [interior_compl, hclosure]
    ext x
    constructor
    · intro hx
      by_cases hxt : x ∈ e.target
      · have hh : (e.symm x).2 ∈ Ioo a b := by
          exact (hsource ▸ e.map_target hxt).2
        have hle : (e.symm x).2 ≤ d := le_of_not_gt fun hgt =>
          hx (Or.inl ((e.mem_cylinderTail_iff hsource hd.1 x).mpr ⟨hxt, hgt, hh.2⟩))
        have hne : (e.symm x).2 ≠ d := fun heq =>
          hx (Or.inr ((hslice x).mpr ⟨hxt, heq⟩))
        exact Or.inr ((hnegative x).mpr ⟨hxt, hh.1, lt_of_le_of_ne hle hne⟩)
      · exact Or.inl hxt
    · rintro (hx | hx) (hxT | hxS)
      · exact hx ((e.mem_cylinderTail_iff hsource hd.1 x).mp hxT).1
      · exact hx ((hslice x).mp hxS).1
      · exact ((hnegative x).mp hx).2.2.not_gt
          ((e.mem_cylinderTail_iff hsource hd.1 x).mp hxT).2.1
      · exact ((hnegative x).mp hx).2.2.ne ((hslice x).mp hxS).2
  have hdiff : (e.cylinderTail b d)ᶜ \ lower = e.cylinderSlice d := by
    rw [← hinterior, interior_compl, hclosure]
    ext x
    simp only [mem_sdiff, mem_compl_iff, mem_union, not_not]
    constructor
    · rintro ⟨hx, hxT | hxS⟩
      · exact (hx hxT).elim
      · exact hxS
    · intro hxS
      exact ⟨fun hxT => disjoint_left.mp hdisjoint hxT hxS, Or.inr hxS⟩
  have hsliceLower : e.cylinderSlice d ⊆ closure lower := by
    have himage : e.IsImage (univ ×ˢ Ioo a d) (e '' (univ ×ˢ Ioo a d)) := by
      apply IsImage.of_image_eq
      rw [inter_eq_right.mpr hdom]
      exact (inter_eq_right.mpr (fun _ hx => by
        obtain ⟨z, hz, rfl⟩ := hx
        exact e.map_source (hdom hz))).symm
    have hfront : e.source ∩ frontier (univ ×ˢ Ioo a d) = univ ×ˢ {d} := by
      rw [hsource, frontier_univ_prod_eq, frontier_Ioo hd.1]
      ext z
      simp only [mem_inter_iff, mem_prod, mem_univ, true_and, mem_Ioo,
        mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hz, hza | hzd⟩
        · exact (hz.1.ne' hza).elim
        · exact hzd
      · intro hzd
        subst hzd
        exact ⟨hd, Or.inr rfl⟩
    have heq : e.target ∩ frontier (e '' (univ ×ˢ Ioo a d)) = e.cylinderSlice d := by
      rw [← himage.frontier.image_eq, hfront]
      rfl
    rw [← heq]
    intro x hx
    exact closure_mono subset_union_right (frontier_subset_closure hx.2)
  have hopen : IsOpen lower := hinterior ▸ isOpen_interior
  have hclosed : IsClosed (e.cylinderTail b d)ᶜ :=
    (e.isOpen_cylinderTail hsource hd.1).isClosed_compl
  have hcl : closure lower = (e.cylinderTail b d)ᶜ := by
    apply Subset.antisymm
    · apply closure_minimal _ hclosed
      rw [← hinterior]
      exact interior_subset
    · intro x hx
      by_cases hxL : x ∈ lower
      · exact subset_closure hxL
      · exact hsliceLower (hdiff ▸ ⟨hx, hxL⟩)
  refine ⟨hopen, hcl, hinterior, ?_, ?_⟩
  · rw [hopen.frontier_eq, hcl]
    exact hdiff
  · rw [frontier, hclosed.closure_eq, hinterior]
    exact hdiff

end OpenPartialHomeomorph
