import PoincareConjecture.Proofs.M47.LimitFinitePreservedSearch
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAgreement











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem exists_source_initial_joined_cylinder
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale a c : ℝ} {U : Set C.carrier}
    (D : SurgeryFlowCylinder F C origin scale (Icc a c) U)
    (e0 : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    (hac : a ≤ c) (hc : c ≤ 0) (hU : IsOpen U) (hne : U.Nonempty)
    (hjoin : ∀ x ∈ U, D.forward c ⟨hac, le_rfl⟩ x =
      e0.forward c ⟨le_rfl, hc⟩ x) :
    ∃ E : SurgeryFlowCylinder F C origin scale (Icc a 0) U,
      (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc a 0) x,
        E.forward s hs' x = e0.forward s hs x) ∧
      ∀ s (hs : s ∈ Icc a c) (hs' : s ∈ Icc a 0) x, x ∈ U →
        E.forward s hs' x = D.forward s hs x := by
  classical
  let x0 := hne.choose
  let Q (s : ℝ) : Prop :=
    ∃ E : SurgeryFlowCylinder F C origin scale (Icc s 0) U,
      ∀ t (ht : t ∈ Icc c 0) (ht' : t ∈ Icc s 0) x,
        E.forward t ht' x = e0.forward t ht x
  have hQc : Q c := ⟨e0, fun _ _ _ _ => rfl⟩
  have hscale := e0.scale_pos
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    simpa only [add_comm] using
      add_lt_add_left ((div_lt_div_iff_of_pos_right hscale).mpr hst) origin
  have hJ : Icc (origin + a / scale) (origin + c / scale) ⊆ F.time_domain := by
    intro z hz
    have hinv : origin + (scale * (z - origin)) / scale = z := by
      rw [mul_div_cancel_left₀ _ hscale.ne', add_sub_cancel]
    have hs : scale * (z - origin) ∈ Icc a c := by
      constructor
      · apply hclock.le_iff_le.mp
        rw [hinv]
        exact hz.1
      · apply hclock.le_iff_le.mp
        rw [hinv]
        exact hz.2
    exact D.time_subset ⟨scale * (z - origin), hs, hinv⟩
  let events : Set ℝ := (fun s : ℝ => origin + s / scale) ⁻¹' F.surgery_times
  have hfinite : (events ∩ Ioc a c).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc hJ
    apply (hf.preimage hclock.injective.injOn).subset
    intro s hs
    exact ⟨hs.1, hclock.monotone hs.2.1.le, hclock.monotone hs.2.2⟩
  have hord : ∀ s ∈ Icc a c, ∀ t ∈ Icc a c, s ≤ t →
      Disjoint events (Ioc s t) → Q t → Q s := by
    intro s hs t ht hst hfree hQt
    obtain ⟨e, he⟩ := hQt
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
      refine ⟨E, ?_⟩
      intro r hr hr' x
      rw [hE r ⟨ht.2.trans hr.1, hr.2⟩ hr' x]
      exact he r hr _ x
    · subst s
      exact ⟨e, he⟩
  have hevent : ∀ t ∈ events ∩ Ioc a c, Q t →
      ∃ d ∈ Icc a t, d < t ∧ Q d := by
    intro t ht hQt
    obtain ⟨e, he⟩ := hQt
    have ht0 : t ≤ 0 := ht.2.2.trans hc
    let : Nonempty (F.slice (origin + t / scale)).carrier :=
      ⟨e.forward t ⟨le_rfl, ht0⟩ x0⟩
    have hT : origin + t / scale ∈ F.surgery_times := ht.1
    let event := F.event (origin + t / scale) hT
    have hagree (x : C.carrier) (hx : x ∈ U) :
        e.forward t ⟨le_rfl, ht0⟩ x = D.forward t ⟨ht.2.1.le, ht.2.2⟩ x := by
      apply source_initial_cylinder_eq_of_terminal e D ht.2.2
        (fun _ hr => ⟨hr.1, hr.2.trans hc⟩)
        (fun _ hr => ⟨ht.2.1.le.trans hr.1, hr.2⟩) x hx x hx
      exact (he c ⟨le_rfl, hc⟩ _ x).trans (hjoin x hx).symm
    have hret : e.forward t ⟨le_rfl, ht0⟩ '' U ⊆ interior event.retained_post := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hagree x hx]
      exact D.retained_at_surgery t ⟨ht.2.1.le, ht.2.2⟩ hT
        ⟨a, ⟨le_rfl, hac⟩, ht.2.1⟩ (mem_image_of_mem _ hx)
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
    refine ⟨d, ⟨had, hdt.le⟩, hdt, E, ?_⟩
    intro r hr hr' x
    rw [hE r ⟨ht.2.2.trans hr.1, hr.2⟩ hr' x]
    exact he r hr _ x
  obtain ⟨E, hE⟩ :=
    Proofs.M46.backward_cylinder_finite_event_induction hac hfinite Q hQc hord hevent
  refine ⟨E, hE, ?_⟩
  intro s hs hs' x hx
  apply source_initial_cylinder_eq_of_terminal E D hs.2
    (fun _ hr => ⟨hs.1.trans hr.1, hr.2.trans hc⟩)
    (fun _ hr => ⟨hs.1.trans hr.1, hr.2⟩) x hx x hx
  exact (hE c ⟨le_rfl, hc⟩ _ x).trans (hjoin x hx).symm

end PoincareConjecture.M47
