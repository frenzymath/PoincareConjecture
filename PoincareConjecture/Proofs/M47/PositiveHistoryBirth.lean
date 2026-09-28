import PoincareConjecture.Proofs.M47.ComponentEstimateBackward
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M47.ComponentHistory

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47Positive

theorem exists_component_birth_cylinder
    (F : SurgeryFlowData.{u}) {origin a : ℝ} (ha : a ≤ 0)
    (hJ : Icc (origin + a) origin ⊆ F.time_domain)
    (U : Set (F.slice origin).carrier) (hU : IsOpen U)
    (hcompact : IsCompact U) (hconnected : IsConnected U) :
    ∃ (b : ℝ) (hb : b ∈ Icc a 0),
      ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc b 0) U,
        (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) ∧
        (b = a ∨ ∃ hT : origin + b / 1 ∈ F.surgery_times,
          ∀ [Nonempty (F.slice (origin + b / 1)).carrier],
            ∃ i : Fin (F.event (origin + b / 1) hT).cap_count,
              (e.forward b ⟨le_rfl, hb.2⟩ '' U ∩
                ((F.event (origin + b / 1) hT).caps i).carrier).Nonempty) := by
  classical
  obtain ⟨x0, hx0⟩ := hconnected.nonempty
  let Stop (b : ℝ) (hb : b ≤ 0)
      (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc b 0) U) : Prop :=
    ∃ hT : origin + b / 1 ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (origin + b / 1)).carrier],
        ∃ i : Fin (F.event (origin + b / 1) hT).cap_count,
          (e.forward b ⟨le_rfl, hb⟩ '' U ∩
            ((F.event (origin + b / 1) hT).caps i).carrier).Nonempty
  let Q (c : ℝ) : Prop := ∃ (b : ℝ) (hb : b ∈ Icc c 0),
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc b 0) U,
      (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) ∧ (b = c ∨ Stop b hb.2 e)
  have horigin : origin ∈ F.time_domain := hJ ⟨by linarith, le_rfl⟩
  obtain ⟨initial, hinitial⟩ := M47.exists_component_singleton_cylinder F origin horigin U
  have hQ0 : Q 0 := ⟨0, ⟨le_rfl, le_rfl⟩, initial, hinitial, Or.inl rfl⟩
  let events : Set ℝ := (fun s : ℝ => origin + s / 1) ⁻¹' F.surgery_times
  have hclock : StrictMono (fun s : ℝ => origin + s / 1) := by
    intro s t hst
    simpa only [div_one, add_comm] using add_lt_add_left hst origin
  have htime : Icc (origin + a / 1) (origin + 0 / 1) ⊆ F.time_domain := by
    simpa only [div_one, add_zero] using hJ
  have hfinite : (events ∩ Ioc a 0).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc htime
    apply (hf.preimage hclock.injective.injOn).subset
    intro s hs
    exact ⟨hs.1, hclock.monotone hs.2.1.le, hclock.monotone hs.2.2⟩
  have hord : ∀ s ∈ Icc a 0, ∀ t ∈ Icc a 0, s ≤ t →
      Disjoint events (Ioc s t) → Q t → Q s := by
    intro s hs t ht hst hfree hQt
    obtain ⟨b, hb, e, he, hstop⟩ := hQt
    rcases hstop with hstart | hstop
    · subst b
      rcases lt_or_eq_of_le hst with hst | heq
      · have hsmall : Icc (origin + s / 1) (origin + t / 1) ⊆ F.time_domain := by
          intro z hz
          exact htime ⟨(hclock.monotone hs.1).trans hz.1,
            hz.2.trans (hclock.monotone ht.2)⟩
        have hfree' : Disjoint F.surgery_times
            (Ioc (origin + s / 1) (origin + t / 1)) := by
          apply Set.disjoint_left.mpr
          intro z hz hzI
          have hze : z - origin ∈ events := by
            simpa only [events, mem_preimage, div_one, add_sub_cancel] using hz
          exact Set.disjoint_left.mp hfree hze
            (by simp only [div_one] at hzI; constructor <;> linarith [hzI.1, hzI.2])
        obtain ⟨E, hE⟩ := Proofs.M46.exists_cylinder_backward_along_ordinary_slab e hU
          ht.2 hst hsmall hfree'
        refine ⟨s, ⟨le_rfl, hs.2⟩, E, ?_, Or.inl rfl⟩
        intro h x hx
        rw [hE 0 ⟨ht.2, le_rfl⟩ h x]
        exact he _ x hx
      · subst s
        exact ⟨t, ⟨le_rfl, ht.2⟩, e, he, Or.inl rfl⟩
    · exact ⟨b, ⟨hst.trans hb.1, hb.2⟩, e, he, Or.inr hstop⟩
  have hevent : ∀ c ∈ events ∩ Ioc a 0, Q c →
      ∃ d ∈ Icc a c, d < c ∧ Q d := by
    intro c hc hQc
    obtain ⟨b, hb, e, he, hstop⟩ := hQc
    have hcarry (hstop : Stop b hb.2 e) : ∃ d ∈ Icc a c, d < c ∧ Q d := by
      obtain ⟨d, had, hdc⟩ := exists_between hc.2.1
      exact ⟨d, ⟨had.le, hdc.le⟩, hdc, b, ⟨hdc.le.trans hb.1, hb.2⟩,
        e, he, Or.inr hstop⟩
    rcases hstop with hstart | hstop
    · subst b
      let : Nonempty (F.slice (origin + c / 1)).carrier :=
        ⟨e.forward c ⟨le_rfl, hc.2.2⟩ x0⟩
      have hT : origin + c / 1 ∈ F.surgery_times := hc.1
      let event := F.event (origin + c / 1) hT
      by_cases hcontact : ∃ i : Fin event.cap_count,
          (e.forward c ⟨le_rfl, hc.2.2⟩ '' U ∩ (event.caps i).carrier).Nonempty
      · apply hcarry
        exact ⟨hT, fun [_] => hcontact⟩
      · have himage := M47.component_cylinder_image_eq e hU hcompact hconnected
          c ⟨le_rfl, hc.2.2⟩ hx0
        have hcapfree : ∀ i : Fin event.cap_count,
            Disjoint (connectedComponent (e.forward c ⟨le_rfl, hc.2.2⟩ x0))
              (event.caps i).carrier := by
          intro i
          rw [← himage]
          exact Set.disjoint_left.mpr fun z hz hzcap => hcontact ⟨i, z, hz, hzcap⟩
        have hret : e.forward c ⟨le_rfl, hc.2.2⟩ '' U ⊆ interior event.retained_post := by
          rw [himage]
          exact M47.capFree_post_component_subset_interior event hcapfree
        let d := max a (event.tMinus - origin)
        have had : a ≤ d := le_max_left _ _
        have hdc : d < c := by
          apply max_lt hc.2.1
          have ht := event.tMinus_lt
          simp only [div_one] at ht
          linarith
        have hd : event.tMinus ≤ origin + d / 1 := by
          have h := le_max_right a (event.tMinus - origin)
          dsimp only [d]
          simp only [div_one]
          linarith
        obtain ⟨E, hE⟩ := M47.exists_component_cylinder_backward_across_retained_event e hU
          hc.2.2 hdc hT hd hret
        refine ⟨d, ⟨had, hdc.le⟩, hdc, d, ⟨le_rfl, hdc.le.trans hc.2.2⟩, E,
          ?_, Or.inl rfl⟩
        intro h x hx
        rw [hE 0 ⟨hc.2.2, le_rfl⟩ h x]
        exact he _ x hx
    · exact hcarry hstop
  exact Proofs.M46.backward_cylinder_finite_event_induction ha hfinite Q hQ0 hord hevent

end PoincareConjecture.M47Positive
