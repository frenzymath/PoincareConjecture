import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_BackwardFiniteEvents
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_BackwardOrdinaryCylinder
import PoincareConjecture.Proofs.M47.ComponentEstimateRetained











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47





theorem exists_component_backward_cylinder_of_retained_frontiers
    {F : SurgeryFlowData.{u}}
    {origin a : ℝ} (ha : a ≤ 0)
    (hJ : Icc (origin + a) origin ⊆ F.time_domain)
    (U : Set (F.slice origin).carrier) (hU : IsOpen U) (hne : U.Nonempty)
    (initial : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc 0 0) U)
    (hinitial : ∀ h x, x ∈ U → HEq (initial.forward 0 h x) x)
    (hfrontier : ∀ c (hc : c ∈ Ioc a 0)
      (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U),
      (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) →
      ∀ (hT : origin + c / 1 ∈ F.surgery_times)
        [Nonempty (F.slice (origin + c / 1)).carrier],
        e.forward c ⟨le_rfl, hc.2⟩ '' U ⊆
          interior (F.event (origin + c / 1) hT).retained_post) :
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc a 0) U,
      ∀ h x, x ∈ U → HEq (e.forward 0 h x) x := by
  classical
  let events : Set ℝ := (fun s : ℝ => origin + s / 1) ⁻¹' F.surgery_times
  let Q : ℝ → Prop := fun c =>
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U,
      ∀ h x, x ∈ U → HEq (e.forward 0 h x) x
  have htime : Icc (origin + a / 1) (origin + 0 / 1) ⊆ F.time_domain := by
    simpa only [div_one, add_zero] using hJ
  have hclock : StrictMono (fun s : ℝ => origin + s / 1) := by
    intro s t hst
    simpa only [div_one, add_comm] using add_lt_add_left hst origin
  have hfinite : (events ∩ Ioc a 0).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc htime
    apply (hf.preimage hclock.injective.injOn).subset
    intro s hs
    exact ⟨hs.1, hclock.monotone hs.2.1.le, hclock.monotone hs.2.2⟩
  apply Proofs.M46.backward_cylinder_finite_event_induction ha hfinite Q ⟨initial, hinitial⟩
  · intro s hs t ht hst hfree hQt
    rcases lt_or_eq_of_le hst with hst | rfl
    · obtain ⟨e, he⟩ := hQt
      have hsmall : Icc (origin + s / 1) (origin + t / 1) ⊆ F.time_domain := by
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
      obtain ⟨E, hE⟩ := Proofs.M46.exists_cylinder_backward_along_ordinary_slab e hU ht.2
        hst hsmall hfree'
      refine ⟨E, ?_⟩
      intro h x hx
      rw [hE 0 ⟨ht.2, le_rfl⟩ h x]
      exact he _ x hx
    · exact hQt
  · intro c hc hQc
    obtain ⟨e, he⟩ := hQc
    obtain ⟨x, hx⟩ := hne
    let : Nonempty (F.slice (origin + c / 1)).carrier :=
      ⟨e.forward c ⟨le_rfl, hc.2.2⟩ x⟩
    have hT : origin + c / 1 ∈ F.surgery_times := hc.1
    let event := F.event (origin + c / 1) hT
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
      simpa only [div_one] using (show event.tMinus ≤ origin +
        max a (event.tMinus - origin) by linarith)
    obtain ⟨E, hE⟩ := exists_component_cylinder_backward_across_retained_event e hU
      hc.2.2 hdc hT hd (hfrontier c hc.2 e he hT)
    refine ⟨d, ⟨had, hdc.le⟩, hdc, E, ?_⟩
    intro h y hy
    rw [hE 0 ⟨hc.2.2, le_rfl⟩ h y]
    exact he _ y hy

end PoincareConjecture.M47
