import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {K W : Type*} [TopologicalSpace K] [TopologicalSpace W]

def cylinderTail (e : OpenPartialHomeomorph (K × ℝ) W) (b d : ℝ) : Set W :=
  e '' (univ ×ˢ Ioo d b)

def cylinderSlice (e : OpenPartialHomeomorph (K × ℝ) W) (d : ℝ) : Set W :=
  e '' (univ ×ˢ {d})

def cylinderSlab (e : OpenPartialHomeomorph (K × ℝ) W) (d u : ℝ) : Set W :=
  e '' (univ ×ˢ Icc d u)

variable (e : OpenPartialHomeomorph (K × ℝ) W) {a b d u : ℝ}

theorem cylinderTail_antitone (b : ℝ) : Antitone (e.cylinderTail b) := by
  intro d u hdu
  exact image_mono (prod_mono Subset.rfl (Ioo_subset_Ioo_left hdu))

theorem cylinderTail_subset_slab_union_tail (b d u : ℝ) :
    e.cylinderTail b d ⊆ e.cylinderSlab d u ∪ e.cylinderTail b u := by
  rintro x ⟨z, hz, rfl⟩
  by_cases hzu : z.2 ≤ u
  · exact Or.inl ⟨z, ⟨hz.1, hz.2.1.le, hzu⟩, rfl⟩
  · exact Or.inr ⟨z, ⟨hz.1, lt_of_not_ge hzu, hz.2.2⟩, rfl⟩

theorem cylinderTail_domain_subset
    (hsource : e.source = univ ×ˢ Ioo a b) (ha : a < d) :
    univ ×ˢ Ioo d b ⊆ e.source := by
  rw [hsource]
  exact prod_mono Subset.rfl (Ioo_subset_Ioo_left ha.le)

theorem cylinderTail_subset_target
    (hsource : e.source = univ ×ˢ Ioo a b) (ha : a < d) :
    e.cylinderTail b d ⊆ e.target := by
  rintro x ⟨z, hz, rfl⟩
  exact e.map_source (e.cylinderTail_domain_subset hsource ha hz)

theorem mem_cylinderTail_iff
    (hsource : e.source = univ ×ˢ Ioo a b) (ha : a < d) (x : W) :
    x ∈ e.cylinderTail b d ↔ x ∈ e.target ∧ (e.symm x).2 ∈ Ioo d b := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzs := e.cylinderTail_domain_subset hsource ha hz
    refine ⟨e.map_source hzs, ?_⟩
    rw [e.left_inv hzs]
    exact hz.2
  · rintro ⟨hx, ht⟩
    exact ⟨e.symm x, ⟨mem_univ _, ht⟩, e.right_inv hx⟩

theorem isOpen_cylinderTail
    (hsource : e.source = univ ×ˢ Ioo a b) (ha : a < d) :
    IsOpen (e.cylinderTail b d) :=
  e.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
    (e.cylinderTail_domain_subset hsource ha)

theorem isConnected_cylinderTail [ConnectedSpace K]
    (hsource : e.source = univ ×ˢ Ioo a b) (hd : d ∈ Ioo a b) :
    IsConnected (e.cylinderTail b d) :=
  (isConnected_univ.prod (isConnected_Ioo hd.2)).image e
    (e.continuousOn.mono (e.cylinderTail_domain_subset hsource hd.1))

theorem exists_cylinder_height_lt_after
    (hsource : e.source = univ ×ˢ Ioo a b) {Q : Set W}
    (hQ : IsCompact Q) (hQt : Q ⊆ e.target) (hd : d ∈ Ioo a b) :
    ∃ u ∈ Ioo d b, ∀ x ∈ Q, (e.symm x).2 < u := by
  rcases Q.eq_empty_or_nonempty with rfl | hQne
  · obtain ⟨u, hdu, hub⟩ := exists_between hd.2
    exact ⟨u, ⟨hdu, hub⟩, fun _ hx => hx.elim⟩
  · obtain ⟨x, hx, hmax⟩ := hQ.exists_isMaxOn hQne
      (e.continuousOn_symm.snd.mono hQt)
    have hxb : (e.symm x).2 < b := by
      have hxs := e.map_target (hQt hx)
      rw [hsource] at hxs
      exact hxs.2.2
    obtain ⟨u, hu, hub⟩ := exists_between (max_lt hd.2 hxb)
    exact ⟨u, ⟨(le_max_left _ _).trans_lt hu, hub⟩,
      fun y hy => (hmax hy).trans_lt ((le_max_right _ _).trans_lt hu)⟩

theorem target_inter_frontier_cylinderTail
    (hsource : e.source = univ ×ˢ Ioo a b) (hd : d ∈ Ioo a b) :
    e.target ∩ frontier (e.cylinderTail b d) = e.cylinderSlice d := by
  have himage : e.IsImage (univ ×ˢ Ioo d b) (e.cylinderTail b d) := by
    apply IsImage.of_image_eq
    rw [inter_eq_right.mpr (e.cylinderTail_domain_subset hsource hd.1),
      inter_eq_right.mpr (e.cylinderTail_subset_target hsource hd.1)]
    rfl
  have hfrontier : e.source ∩ frontier (univ ×ˢ Ioo d b) = univ ×ˢ {d} := by
    rw [hsource, frontier_univ_prod_eq, frontier_Ioo hd.2]
    ext z
    simp only [mem_inter_iff, mem_prod, mem_univ, true_and, mem_Ioo,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzd | hzb⟩
      · exact hzd
      · exact (hz.2.ne hzb).elim
    · intro hzd
      subst hzd
      exact ⟨hd, Or.inl rfl⟩
  rw [← himage.frontier.image_eq, hfrontier]
  rfl

theorem cylinderSlab_subset_target
    (hsource : e.source = univ ×ˢ Ioo a b) (ha : a < d) (hb : u < b) :
    e.cylinderSlab d u ⊆ e.target := by
  rintro x ⟨z, hz, rfl⟩
  apply e.map_source
  rw [hsource]
  exact ⟨hz.1, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem isCompact_cylinderSlab [CompactSpace K]
    (hsource : e.source = univ ×ˢ Ioo a b) (ha : a < d) (hb : u < b) :
    IsCompact (e.cylinderSlab d u) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply e.continuousOn.mono
  intro z hz
  rw [hsource]
  exact ⟨hz.1, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

end OpenPartialHomeomorph
