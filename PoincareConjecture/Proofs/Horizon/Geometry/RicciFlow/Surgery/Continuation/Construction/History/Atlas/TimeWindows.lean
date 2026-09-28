import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.RegularSlices










set_option autoImplicit false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory

theorem nontrivial_inter_Ioo {J : Set ℝ} (hJ : J.OrdConnected) (hne : J.Nontrivial)
    {t a b : ℝ} (ht : t ∈ J) (ha : a < t) (hb : t < b) :
    (J ∩ Ioo a b).Nontrivial := by
  obtain ⟨s, hs, hst⟩ := hne.exists_ne t
  rcases lt_or_gt_of_ne hst with hst | hts
  · let r := (max s a + t) / 2
    have hr : max s a < r ∧ r < t := by
      dsimp [r]
      have hmax := max_lt hst ha
      constructor <;> linarith
    exact ⟨r, ⟨hJ.out hs ht ⟨(le_max_left _ _).trans hr.1.le, hr.2.le⟩,
      (le_max_right _ _).trans_lt hr.1, hr.2.trans hb⟩,
      t, ⟨ht, ha, hb⟩, hr.2.ne⟩
  · let r := (t + min s b) / 2
    have hr : t < r ∧ r < min s b := by
      dsimp [r]
      have hmin := lt_min hts hb
      constructor <;> linarith
    exact ⟨t, ⟨ht, ha, hb⟩,
      r, ⟨hJ.out ht hs ⟨hr.1.le, hr.2.le.trans (min_le_left _ _)⟩,
      ha.trans hr.1, hr.2.trans_le (min_le_right _ _)⟩, hr.1.ne⟩

private theorem exists_left_bound {J : Set ℝ} (hJ : J.OrdConnected)
    {t l : ℝ} (ht : t ∈ J) (hl : l < t) :
    ∃ a ∈ J, l < a ∧ a ≤ t ∧ (a < t ∨ ∀ s ∈ J, t ≤ s) := by
  by_cases h : ∃ s ∈ J, s < t
  · obtain ⟨s, hs, hst⟩ := h
    let a := (max l s + t) / 2
    have ha : max l s < a ∧ a < t := by
      dsimp [a]
      have hm := max_lt hl hst
      constructor <;> linarith
    exact ⟨a, hJ.out hs ht ⟨(le_max_right _ _).trans ha.1.le, ha.2.le⟩,
      (le_max_left _ _).trans_lt ha.1, ha.2.le, Or.inl ha.2⟩
  · refine ⟨t, ht, hl, le_rfl, Or.inr ?_⟩
    intro s hs
    exact le_of_not_gt (fun hst => h ⟨s, hs, hst⟩)

private theorem exists_right_bound {J : Set ℝ} (hJ : J.OrdConnected)
    {t r : ℝ} (ht : t ∈ J) (hr : t < r) :
    ∃ b ∈ J, b < r ∧ t ≤ b ∧ (t < b ∨ ∀ s ∈ J, s ≤ t) := by
  by_cases h : ∃ s ∈ J, t < s
  · obtain ⟨s, hs, hts⟩ := h
    let b := (t + min r s) / 2
    have hb : t < b ∧ b < min r s := by
      dsimp [b]
      have hm := lt_min hr hts
      constructor <;> linarith
    exact ⟨b, hJ.out ht hs ⟨hb.1.le, hb.2.le.trans (min_le_right _ _)⟩,
      hb.2.trans_le (min_le_left _ _), hb.1.le, Or.inl hb.1⟩
  · refine ⟨t, ht, hr, le_rfl, Or.inr ?_⟩
    intro s hs
    exact le_of_not_gt (fun hts => h ⟨s, hs, hts⟩)

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)

theorem exists_regular_neighborhood {t : ℝ} (hT : t ∉ F.surgery_times) :
    ∃ l r : ℝ, l < t ∧ t < r ∧
      Disjoint F.surgery_times (W.interval ∩ Ioo l r) := by
  have ht : t ∈ (F.surgery_times ∩ W.interval)ᶜ := fun h => hT h.1
  obtain ⟨l, r, hlt, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (W.events_finite.isClosed.isOpen_compl.mem_nhds ht)
  refine ⟨l, r, hlt.1, hlt.2, disjoint_left.mpr ?_⟩
  intro s hs hJ
  exact hsub hJ.2 ⟨hs, hJ.1⟩



theorem exists_regular_slab_window {t : ℝ} (ht : t ∈ W.interval)
    (hT : t ∉ F.surgery_times) :
    ∃ a b : ℝ, a < b ∧ Icc a b ⊆ W.interval ∧
      Disjoint F.surgery_times (Icc a b) ∧
      ∃ c d : ℝ, c < t ∧ t < d ∧ W.interval ∩ Ioo c d ⊆ Icc a b := by
  obtain ⟨l, r, hlt, htr, hfree⟩ := exists_regular_neighborhood W hT
  obtain ⟨a, ha, hla, hat, hleft⟩ := exists_left_bound W.interval_connected ht hlt
  obtain ⟨b, hb, hbr, htb, hright⟩ := exists_right_bound W.interval_connected ht htr
  have hab : a < b := by
    rcases hleft with hleft | hleft
    · exact hleft.trans_le htb
    rcases hright with hright | hright
    · exact hat.trans_lt hright
    obtain ⟨s, hs, hst⟩ := W.interval_nontrivial.exists_ne t
    exact (hst (le_antisymm (hright s hs) (hleft s hs))).elim
  have hsub : Icc a b ⊆ W.interval := W.interval_connected.out ha hb
  refine ⟨a, b, hab, hsub, hfree.mono_right ?_, ?_⟩
  · intro s hs
    exact ⟨hsub hs, hla.trans_le hs.1, hs.2.trans_lt hbr⟩
  · rcases hleft with hleft | hleft
    · rcases hright with hright | hright
      · exact ⟨a, b, hleft, hright, fun _ hs => ⟨hs.2.1.le, hs.2.2.le⟩⟩
      · exact ⟨a, t + 1, hleft, by linarith,
          fun s hs => ⟨hs.2.1.le, (hright s hs.1).trans htb⟩⟩
    · rcases hright with hright | hright
      · exact ⟨t - 1, b, by linarith, hright,
          fun s hs => ⟨hat.trans (hleft s hs.1), hs.2.2.le⟩⟩
      · exact ⟨t - 1, t + 1, by linarith, by linarith,
          fun s hs => ⟨hat.trans (hleft s hs.1), (hright s hs.1).trans htb⟩⟩


structure OrdinaryTimeWindow where
  lower : ℝ
  upper : ℝ
  left : ℝ
  right : ℝ
  ordered : lower < upper
  slab_subset : Icc lower upper ⊆ W.interval
  surgery_free : Disjoint F.surgery_times (Icc lower upper)
  interval_subset : W.interval ∩ Ioo left right ⊆ Icc lower upper
  interval_nontrivial : (W.interval ∩ Ioo left right).Nontrivial

variable {W}

def OrdinaryTimeWindow.interval (A : OrdinaryTimeWindow W) : Set ℝ :=
  W.interval ∩ Ioo A.left A.right

theorem OrdinaryTimeWindow.interval_connected (A : OrdinaryTimeWindow W) :
    A.interval.OrdConnected := W.interval_connected.inter ordConnected_Ioo

theorem OrdinaryTimeWindow.time_subset (A : OrdinaryTimeWindow W) :
    A.interval ⊆ W.interval := inter_subset_left

theorem OrdinaryTimeWindow.regular (A : OrdinaryTimeWindow W) {t : ℝ}
    (ht : t ∈ A.interval) : t ∉ F.surgery_times :=
  fun hT => disjoint_left.mp A.surgery_free hT (A.interval_subset ht)

variable (W)

theorem exists_ordinaryTimeWindow {t : ℝ} (ht : t ∈ W.interval)
    (hT : t ∉ F.surgery_times) : ∃ A : OrdinaryTimeWindow W, t ∈ A.interval := by
  obtain ⟨a, b, hab, hsub, hfree, c, d, hct, htd, hbox⟩ :=
    exists_regular_slab_window W ht hT
  exact ⟨⟨a, b, c, d, hab, hsub, hfree, hbox,
    nontrivial_inter_Ioo W.interval_connected W.interval_nontrivial ht hct htd⟩,
    ht, hct, htd⟩

end PoincareConjecture.Surgery.RegularHistory
