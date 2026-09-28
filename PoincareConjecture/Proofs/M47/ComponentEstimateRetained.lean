import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M47.ComponentEstimateIntervals












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47




theorem exists_component_cylinder_backward_across_retained_event
    {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin scale c d : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    (hU : IsOpen U) (hc : c ≤ 0) (_hdc : d < c)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hd : (F.event (origin + c / scale) hT).tMinus ≤ origin + d / scale)
    (hret : e.forward c ⟨le_rfl, hc⟩ '' U ⊆
      interior (F.event (origin + c / scale) hT).retained_post) :
    ∃ E : SurgeryFlowCylinder F C origin scale (Icc d 0) U,
      ∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc d 0) x,
        E.forward s hs' x = e.forward s hs x := by
  classical
  let event := F.event (origin + c / scale) hT
  let retention := M44.regionEquivalenceInteriorChart event.retention
  let bridge := (M44.cylinderSliceChart e hU c ⟨le_rfl, hc⟩).trans retention.symm
  have hbridge : bridge.source = U := by
    change U ∩ (e.forward c ⟨le_rfl, hc⟩) ⁻¹' interior event.retained_post = U
    exact inter_eq_left.mpr (fun x hx => hret (mem_image_of_mem _ hx))
  have hbridge_retained (x : C.carrier) (hx : x ∈ U) :
      bridge x ∈ interior event.retained_pre :=
    retention.map_target (hret (mem_image_of_mem _ hx))
  have hbridge_right (x : C.carrier) (hx : x ∈ U) :
      event.retention.map (bridge x) = e.forward c ⟨le_rfl, hc⟩ x :=
    retention.right_inv (hret (mem_image_of_mem _ hx))
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    simpa only [add_comm] using
      add_lt_add_left ((div_lt_div_iff_of_pos_right e.scale_pos).mpr hst) origin
  have hpreTime (s : ℝ) (hds : d ≤ s) (hsc : s < c) :
      origin + s / scale ∈ Ico event.tMinus (origin + c / scale) :=
    ⟨hd.trans (hclock.monotone hds), hclock hsc⟩
  let chart (s : ℝ) (hs : s ∈ Icc d 0) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
        (F.slice (origin + s / scale)).carrier ∞ :=
    if hcs : c ≤ s then M44.cylinderSliceChart e hU s ⟨hcs, hs.2⟩
    else bridge.trans (event.pre_identify
      ⟨origin + s / scale, hpreTime s hs.1 (lt_of_not_ge hcs)⟩).toPartialDiffeomorph
  have hsource (s : ℝ) (hs : s ∈ Icc d 0) : (chart s hs).source = U := by
    dsimp only [chart]
    split_ifs
    · rfl
    · change bridge.source ∩ bridge ⁻¹' (univ : Set (F.slice event.tMinus).carrier) = U
      simp only [preimage_univ, inter_univ, hbridge]
  have hold (s : ℝ) (hs : s ∈ Icc d 0) (hcs : c ≤ s) (x : C.carrier) :
      chart s hs x = e.forward s ⟨hcs, hs.2⟩ x := by
    dsimp only [chart]
    rw [dif_pos hcs]
    rfl
  have hnew (s : ℝ) (hs : s ∈ Icc d 0) (hsc : s < c) (x : C.carrier) :
      chart s hs x = event.pre_identify
        ⟨origin + s / scale, hpreTime s hs.1 hsc⟩ (bridge x) := by
    dsimp only [chart]
    rw [dif_neg (not_le_of_gt hsc)]
    rfl
  have hfirst_event (s : ℝ) (hs : s ∈ Icc d 0) (hsc : s < c)
      (hS : origin + s / scale ∈ F.surgery_times) : s = d := by
    apply le_antisymm _ hs.1
    by_contra hsd
    exact Set.disjoint_left.mp (component_event_preterminal_surgery_free F hT) hS
      ⟨hd.trans_lt (hclock (lt_of_not_ge hsd)), hclock hsc⟩
  have hno_cross (s : ℝ) (hcs : c < s)
      (hS : origin + s / scale ∈ F.surgery_times)
      [Nonempty (F.slice (origin + s / scale)).carrier]
      (t : ℝ) (htc : t < c)
      (ht' : origin + t / scale ∈ Ico
        (F.event (origin + s / scale) hS).tMinus (origin + s / scale)) : False :=
    Set.disjoint_left.mp (component_event_preterminal_surgery_free F hS) hT
      ⟨ht'.1.trans_lt (hclock htc), hclock hcs⟩
  have hprefix : Icc 0 (origin + c / scale) ⊆ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
  let E : SurgeryFlowCylinder F C origin scale (Icc d 0) U := {
    scale_pos := e.scale_pos
    interval_connected := ordConnected_Icc
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hcs : c ≤ s
      · exact e.time_subset (mem_image_of_mem _ ⟨hcs, hs.2⟩)
      · have ht := hpreTime s hs.1 (lt_of_not_ge hcs)
        exact hprefix ⟨event.tMinus_nonnegative.trans ht.1, ht.2.le⟩
    forward := fun s hs => chart s hs
    inverse := fun s hs => (chart s hs).symm
    forward_smooth := by
      intro s hs
      simpa only [hsource] using (chart s hs).contMDiffOn
    inverse_smooth := by
      intro s hs
      have himage : chart s hs '' U = (chart s hs).target := by
        rw [← hsource s hs]
        exact (chart s hs).toPartialEquiv.image_source_eq_target
      rw [himage]
      exact (chart s hs).contMDiffOn_invFun
    left_inverse := by
      intro s hs x hx
      exact (chart s hs).left_inv (hsource s hs ▸ hx)
    right_inverse := by
      intro s hs y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact (chart s hs).right_inv ((chart s hs).map_source (hsource s hs ▸ hx))
    slab_compatibility := by
      intro a b hab hJ hfree s hs t ht hs' ht' x hx
      by_cases hcs : c ≤ s
      · by_cases hct : c ≤ t
        · rw [hold s hs hcs x, hold t ht hct x]
          exact e.slab_compatibility a b hab hJ hfree
            s ⟨hcs, hs.2⟩ t ⟨hct, ht.2⟩ hs' ht' x hx
        · exact (Set.disjoint_left.mp hfree hT
            ⟨ht'.1.trans_lt (hclock (lt_of_not_ge hct)),
              (hclock.monotone hcs).trans hs'.2⟩).elim
      · by_cases hct : c ≤ t
        · exact (Set.disjoint_left.mp hfree hT
            ⟨hs'.1.trans_lt (hclock (lt_of_not_ge hcs)),
              (hclock.monotone hct).trans ht'.2⟩).elim
        · rw [hnew s hs (lt_of_not_ge hcs) x, hnew t ht (lt_of_not_ge hct) x]
          exact F.event_slab_compatibility _ hT a b hab hJ hfree
            _ _ hs' ht' (hpreTime s hs.1 (lt_of_not_ge hcs))
            (hpreTime t ht.1 (lt_of_not_ge hct)) (bridge x)
    retained_at_surgery := by
      intro s hs hS _ hearlier
      by_cases hcs : c ≤ s
      · rintro _ ⟨x, hx, rfl⟩
        rw [hold s hs hcs x]
        rcases eq_or_lt_of_le hcs with heq | hlt
        · subst s
          exact hret (mem_image_of_mem _ hx)
        · exact e.retained_at_surgery s ⟨hcs, hs.2⟩ hS
            ⟨c, ⟨le_rfl, hc⟩, hlt⟩ (mem_image_of_mem _ hx)
      · have hsd := hfirst_event s hs (lt_of_not_ge hcs) hS
        obtain ⟨t, ht, hts⟩ := hearlier
        exact (not_lt_of_ge ht.1 (hsd ▸ hts)).elim
    pre_retained_at_surgery := by
      intro s hs hS _ t ht ht' x hx
      have hts : t < s := hclock.lt_iff_lt.mp ht'.2
      by_cases hcs : c ≤ s
      · rcases eq_or_lt_of_le hcs with heq | hlt
        · subst s
          rw [hnew t ht hts x, Diffeomorph.symm_apply_apply]
          exact hbridge_retained x hx
        · by_cases hct : c ≤ t
          · rw [hold t ht hct x]
            exact e.pre_retained_at_surgery s ⟨hcs, hs.2⟩ hS
              t ⟨hct, ht.2⟩ ht' x hx
          · exact (hno_cross s hlt hS t (lt_of_not_ge hct) ht').elim
      · have hsd := hfirst_event s hs (lt_of_not_ge hcs) hS
        exact (not_lt_of_ge ht.1 (hsd ▸ hts)).elim
    surgery_compatibility := by
      intro s hs hS _ t ht ht' x hx
      have hts : t < s := hclock.lt_iff_lt.mp ht'.2
      by_cases hcs : c ≤ s
      · rcases eq_or_lt_of_le hcs with heq | hlt
        · subst s
          rw [hnew t ht hts x, Diffeomorph.symm_apply_apply, hold c hs le_rfl x]
          exact hbridge_right x hx
        · by_cases hct : c ≤ t
          · rw [hold t ht hct x, hold s hs hcs x]
            exact e.surgery_compatibility s ⟨hcs, hs.2⟩ hS
              t ⟨hct, ht.2⟩ ht' x hx
          · exact (hno_cross s hlt hS t (lt_of_not_ge hct) ht').elim
      · have hsd := hfirst_event s hs (lt_of_not_ge hcs) hS
        exact (not_lt_of_ge ht.1 (hsd ▸ hts)).elim
  }
  exact ⟨E, fun s hs hs' x => hold s hs' hs.1 x⟩

end PoincareConjecture.M47
