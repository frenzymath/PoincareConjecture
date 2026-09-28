import PoincareConjecture.Proofs.M47.SeedRetainedSearch










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem limitFinite_exists_preserved_search
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale a c : ℝ} {U : Set C.carrier}
    (e0 : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    (hc : c ≤ 0) (hac : a ≤ c)
    (hJ : Icc (origin + a / scale) (origin + c / scale) ⊆ F.time_domain)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (b : ℝ) (hb : b ∈ Icc a c),
      ∃ E : SurgeryFlowCylinder F C origin scale (Icc b 0) U,
        (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0) x,
          E.forward s hs' x = e0.forward s hs x) ∧
        (b = a ∨ ∃ hT : origin + b / scale ∈ F.surgery_times,
          ∀ [Nonempty (F.slice (origin + b / scale)).carrier],
            ∃ i : Fin (F.event (origin + b / scale) hT).cap_count,
              (E.forward b ⟨le_rfl, hb.2.trans hc⟩ '' U ∩
                ((F.event (origin + b / scale) hT).caps i).carrier).Nonempty) := by
  classical
  let x0 := hne.choose
  let Stop (b : ℝ) (hb : b ≤ 0)
      (e : SurgeryFlowCylinder F C origin scale (Icc b 0) U) : Prop :=
    ∃ hT : origin + b / scale ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (origin + b / scale)).carrier],
        ∃ i : Fin (F.event (origin + b / scale) hT).cap_count,
          (e.forward b ⟨le_rfl, hb⟩ '' U ∩
            ((F.event (origin + b / scale) hT).caps i).carrier).Nonempty
  let Q (s : ℝ) : Prop := ∃ (b : ℝ) (hb : b ∈ Icc s c),
    ∃ e : SurgeryFlowCylinder F C origin scale (Icc b 0) U,
      (∀ t (ht : t ∈ Icc c 0) (ht' : t ∈ Icc b 0) x,
        e.forward t ht' x = e0.forward t ht x) ∧
      (b = s ∨ Stop b (hb.2.trans hc) e)
  have hQc : Q c := ⟨c, ⟨le_rfl, le_rfl⟩, e0, fun _ _ _ _ => rfl, Or.inl rfl⟩
  have hscale := e0.scale_pos
  let events : Set ℝ := (fun s : ℝ => origin + s / scale) ⁻¹' F.surgery_times
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    simpa only [add_comm] using
      add_lt_add_left ((div_lt_div_iff_of_pos_right hscale).mpr hst) origin
  have hfinite : (events ∩ Ioc a c).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc hJ
    apply (hf.preimage hclock.injective.injOn).subset
    intro s hs
    exact ⟨hs.1, hclock.monotone hs.2.1.le, hclock.monotone hs.2.2⟩
  have hord : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c, s ≤ t →
      Disjoint events (Ioc s t) → Q t → Q s := by
    intro s hs t ht hst hfree hQt
    obtain ⟨b, hb, e, he, hstop⟩ := hQt
    rcases hstop with hstart | hstop
    · subst b
      rcases lt_or_eq_of_le hst with hst | heq
      · have hsmall : Icc (origin + s / scale) (origin + t / scale) ⊆
            F.time_domain := by
          intro z hz
          exact hJ ⟨(hclock.monotone hs.1).trans hz.1,
            hz.2.trans (hclock.monotone ht.2)⟩
        have hfree' : Disjoint F.surgery_times
            (Ioc (origin + s / scale) (origin + t / scale)) := by
          apply Set.disjoint_left.mpr
          intro z hz hzI
          have hinv : origin + (scale * (z - origin)) / scale = z := by
            rw [mul_div_cancel_left₀ _ hscale.ne', add_sub_cancel]
          have hze : scale * (z - origin) ∈ events := by
            change origin + (scale * (z - origin)) / scale ∈ F.surgery_times
            rwa [hinv]
          apply Set.disjoint_left.mp hfree hze
          constructor
          · apply hclock.lt_iff_lt.mp
            rw [hinv]
            exact hzI.1
          · apply hclock.le_iff_le.mp
            rw [hinv]
            exact hzI.2
        obtain ⟨E, hE⟩ := Proofs.M46.exists_cylinder_backward_along_ordinary_slab
          e hU (ht.2.trans hc) hst hsmall hfree'
        refine ⟨s, ⟨le_rfl, hs.2⟩, E, ?_, Or.inl rfl⟩
        intro r hr hr' x
        rw [hE r ⟨ht.2.trans hr.1, hr.2⟩ hr' x]
        exact he r hr _ x
      · subst s
        exact ⟨t, ⟨le_rfl, ht.2⟩, e, he, Or.inl rfl⟩
    · exact ⟨b, ⟨hst.trans hb.1, hb.2⟩, e, he, Or.inr hstop⟩
  have hevent : ∀ t ∈ events ∩ Ioc a c, Q t →
      ∃ d ∈ Icc a t, d < t ∧ Q d := by
    intro t ht hQt
    obtain ⟨b, hb, e, he, hstop⟩ := hQt
    have hcarry (hstop : Stop b (hb.2.trans hc) e) :
        ∃ d ∈ Icc a t, d < t ∧ Q d := by
      obtain ⟨d, had, hdt⟩ := exists_between ht.2.1
      exact ⟨d, ⟨had.le, hdt.le⟩, hdt, b, ⟨hdt.le.trans hb.1, hb.2⟩,
        e, he, Or.inr hstop⟩
    rcases hstop with hstart | hstop
    · subst b
      have ht0 : t ≤ 0 := ht.2.2.trans hc
      let : Nonempty (F.slice (origin + t / scale)).carrier :=
        ⟨e.forward t ⟨le_rfl, ht0⟩ x0⟩
      have hT : origin + t / scale ∈ F.surgery_times := ht.1
      let event := F.event (origin + t / scale) hT
      by_cases hcontact : ∃ i : Fin event.cap_count,
          (e.forward t ⟨le_rfl, ht0⟩ '' U ∩ (event.caps i).carrier).Nonempty
      · exact hcarry ⟨hT, fun [_] => hcontact⟩
      · let chart := (M44.cylinderSliceChart e hU t ⟨le_rfl, ht0⟩).toOpenPartialHomeomorph
        have hopen : IsOpen (e.forward t ⟨le_rfl, ht0⟩ '' U) :=
          chart.isOpen_image_of_subset_source hU (Subset.refl U)
        have hret : e.forward t ⟨le_rfl, ht0⟩ '' U ⊆ interior event.retained_post := by
          apply hopen.subset_interior_iff.mpr
          intro z hz
          have hcover : z ∈ event.retained_post ∪ (⋃ i, (event.caps i).carrier) := by
            rw [event.post_cover]
            exact mem_univ z
          apply hcover.resolve_right
          intro hcap
          obtain ⟨i, hi⟩ := mem_iUnion.mp hcap
          exact hcontact ⟨i, z, hz, hi⟩
        let d := max a (scale * (event.tMinus - origin))
        have had : a ≤ d := le_max_left _ _
        have hdt : d < t := by
          apply max_lt ht.2.1
          have hpre : event.tMinus - origin < t / scale := by
            linarith [event.tMinus_lt]
          simpa only [mul_comm] using (lt_div_iff₀ hscale).mp hpre
        have hd : event.tMinus ≤ origin + d / scale := by
          have hmul : (event.tMinus - origin) * scale ≤ d := by
            simpa only [mul_comm] using le_max_right a (scale * (event.tMinus - origin))
          have hdiv := (le_div_iff₀ hscale).mpr hmul
          linarith
        obtain ⟨E, hE⟩ := exists_component_cylinder_backward_across_retained_event
          e hU ht0 hdt hT hd hret
        refine ⟨d, ⟨had, hdt.le⟩, hdt, d, ⟨le_rfl, hdt.le.trans ht.2.2⟩, E,
          ?_, Or.inl rfl⟩
        intro r hr hr' x
        rw [hE r ⟨ht.2.2.trans hr.1, hr.2⟩ hr' x]
        exact he r hr _ x
    · exact hcarry hstop
  exact Proofs.M46.backward_cylinder_finite_event_induction hac hfinite Q hQc hord hevent

end PoincareConjecture.M47
