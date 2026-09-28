import PoincareConjecture.Proofs.M48.ExtensionEvents









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}


noncomputable def pushCylinder (d : SurgeryFlowCylinder F C a q J U) :
    SurgeryFlowCylinder E.extended C a q J U := by
  classical
  let f (s : ℝ) (hs : s ∈ J) := E.identify (a + s / q) (d.time_subset ⟨s, hs, rfl⟩)
  refine {
    scale_pos := d.scale_pos
    interval_connected := d.interval_connected
    time_subset := d.time_subset.trans E.old_times
    forward := fun s hs => f s hs ∘ d.forward s hs
    inverse := fun s hs => d.inverse s hs ∘ (f s hs).symm
    forward_smooth := fun s hs => (f s hs).contMDiff.comp_contMDiffOn (d.forward_smooth s hs)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    slab_compatibility := E.cylinder_slab_compatibility d
    retained_at_surgery := ?_
    pre_retained_at_surgery := ?_
    surgery_compatibility := ?_ }
  · intro s hs
    apply (d.inverse_smooth s hs).comp (f s hs).symm.contMDiff.contMDiffOn
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · intro s hs x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using
      d.left_inverse s hs hx
  · intro s hs y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [Diffeomorph.symm_apply_apply, d.left_inverse s hs hx]
  · intro s hs hT hne hearlier
    let _ : Nonempty (F.slice (a + s / q)).carrier := Nonempty.map (f s hs).symm hne
    have hTold := (E.old_surgery_times _ (d.time_subset ⟨s, hs, rfl⟩)).mp hT
    rintro _ ⟨x, hx, rfl⟩
    rw [← E.identify_retained_post_interior hTold hT]
    exact ⟨d.forward s hs x,
      d.retained_at_surgery s hs hTold hearlier ⟨x, hx, rfl⟩, rfl⟩
  · intro s hs hT hne t ht ht' x hx
    let _ : Nonempty (F.slice (a + s / q)).carrier := Nonempty.map (f s hs).symm hne
    have hTold := (E.old_surgery_times _ (d.time_subset ⟨s, hs, rfl⟩)).mp hT
    have htold : a + t / q ∈ Ico (F.event (a + s / q) hTold).tMinus (a + s / q) := by
      simpa only [E.old_event_reference _ hTold hT] using ht'
    rw [← E.eventPreEquivalence_interior hTold hT ⟨_, htold⟩
      (d.time_subset ⟨t, ht, rfl⟩) ht']
    refine ⟨((F.event _ hTold).pre_identify ⟨_, htold⟩).symm (d.forward t ht x),
      d.pre_retained_at_surgery s hs hTold t ht htold x hx, ?_⟩
    simp only [eventPreEquivalence_apply, Diffeomorph.apply_symm_apply]
    rfl
  · intro s hs hT hne t ht ht' x hx
    let _ : Nonempty (F.slice (a + s / q)).carrier := Nonempty.map (f s hs).symm hne
    have hTold := (E.old_surgery_times _ (d.time_subset ⟨s, hs, rfl⟩)).mp hT
    have htold : a + t / q ∈ Ico (F.event (a + s / q) hTold).tMinus (a + s / q) := by
      simpa only [E.old_event_reference _ hTold hT] using ht'
    have hret := E.old_retention _ hTold hT ⟨_, htold⟩
      (d.time_subset ⟨t, ht, rfl⟩) ht'
      (((F.event _ hTold).pre_identify ⟨_, htold⟩).symm (d.forward t ht x))
      (interior_subset (d.pre_retained_at_surgery s hs hTold t ht htold x hx))
    simpa only [Function.comp_apply, f, Diffeomorph.apply_symm_apply,
      d.surgery_compatibility s hs hTold t ht htold x hx] using hret.symm

theorem pushCylinder_forward (d : SurgeryFlowCylinder F C a q J U)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (E.pushCylinder d).forward s hs x =
      E.identify (a + s / q) (d.time_subset ⟨s, hs, rfl⟩) (d.forward s hs x) := rfl



noncomputable def pullCylinder
    (d : SurgeryFlowCylinder E.extended C a q J U)
    (htime : ∀ s ∈ J, a + s / q ∈ F.time_domain) :
    SurgeryFlowCylinder F C a q J U := by
  classical
  let f (s : ℝ) (hs : s ∈ J) := E.identify (a + s / q) (htime s hs)
  refine {
    scale_pos := d.scale_pos
    interval_connected := d.interval_connected
    time_subset := ?_
    forward := fun s hs => (f s hs).symm ∘ d.forward s hs
    inverse := fun s hs => d.inverse s hs ∘ f s hs
    forward_smooth := fun s hs => (f s hs).symm.contMDiff.comp_contMDiffOn
      (d.forward_smooth s hs)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    slab_compatibility := ?_
    retained_at_surgery := ?_
    pre_retained_at_surgery := ?_
    surgery_compatibility := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    exact htime s hs
  · intro s hs
    apply (d.inverse_smooth s hs).comp (f s hs).contMDiff.contMDiffOn
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · intro s hs x hx
    simpa only [Function.comp_apply, Diffeomorph.apply_symm_apply] using
      d.left_inverse s hs hx
  · intro s hs y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [Diffeomorph.apply_symm_apply, d.left_inverse s hs hx]
  · intro l r hlr hJ hfree s hs t ht hs' ht' x hx
    have hnewfree : Disjoint E.extended.surgery_times (Ioc l r) := by
      rw [Set.disjoint_left]
      intro z hz hzi
      exact Set.disjoint_left.mp hfree
        ((E.old_surgery_times z (hJ ⟨hzi.1.le, hzi.2⟩)).mp hz) hzi
    apply (f t ht).injective
    change E.identify (a + t / q) _
      ((F.regular_slabs l r hlr hJ hfree).transport ⟨_, hs'⟩ ⟨_, ht'⟩
        ((f s hs).symm (d.forward s hs x))) = _
    rw [← E.ordinary_compatibility l r hlr hJ hfree (hJ.trans E.old_times)
      hnewfree ⟨_, hs'⟩ ⟨_, ht'⟩]
    change (E.extended.regular_slabs l r hlr (hJ.trans E.old_times) hnewfree).transport
      ⟨_, hs'⟩ ⟨_, ht'⟩ ((f s hs) ((f s hs).symm (d.forward s hs x))) =
        (f t ht) ((f t ht).symm (d.forward t ht x))
    rw [Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]
    exact d.slab_compatibility l r hlr (hJ.trans E.old_times) hnewfree s hs t ht hs' ht' x hx
  · intro s hs hT hne hearlier
    let _ : Nonempty (E.extended.slice (a + s / q)).carrier := Nonempty.map (f s hs) hne
    have hTnew := (E.old_surgery_times _ (htime s hs)).mpr hT
    rintro _ ⟨x, hx, rfl⟩
    have hmem := d.retained_at_surgery s hs hTnew hearlier ⟨x, hx, rfl⟩
    rw [← E.identify_retained_post_interior hT hTnew] at hmem
    rcases hmem with ⟨y, hy, heq⟩
    change (f s hs).symm (d.forward s hs x) ∈ _
    rw [← heq]
    simpa only [f, Diffeomorph.symm_apply_apply] using hy
  · intro s hs hT hne t ht ht' x hx
    let _ : Nonempty (E.extended.slice (a + s / q)).carrier := Nonempty.map (f s hs) hne
    have hTnew := (E.old_surgery_times _ (htime s hs)).mpr hT
    have htnew : a + t / q ∈ Ico (E.extended.event (a + s / q) hTnew).tMinus
        (a + s / q) := by
      simpa only [E.old_event_reference _ hT hTnew] using ht'
    have hmem := d.pre_retained_at_surgery s hs hTnew t ht htnew x hx
    rw [← E.eventPreEquivalence_interior hT hTnew ⟨_, ht'⟩ (htime t ht) htnew] at hmem
    rcases hmem with ⟨y, hy, heq⟩
    have hy' : (F.event _ hT).pre_identify ⟨_, ht'⟩ y =
        (f t ht).symm (d.forward t ht x) := by
      apply (f t ht).injective
      change (f t ht) ((F.event _ hT).pre_identify ⟨_, ht'⟩ y) =
        (f t ht) ((f t ht).symm (d.forward t ht x))
      have hh := congrArg ((E.extended.event _ hTnew).pre_identify ⟨_, htnew⟩) heq
      simpa only [f, eventPreEquivalence_apply, Diffeomorph.apply_symm_apply] using hh
    change ((F.event _ hT).pre_identify ⟨_, ht'⟩).symm
      ((f t ht).symm (d.forward t ht x)) ∈ _
    rw [← hy', Diffeomorph.symm_apply_apply]
    exact hy
  · intro s hs hT hne t ht ht' x hx
    let _ : Nonempty (E.extended.slice (a + s / q)).carrier := Nonempty.map (f s hs) hne
    have hTnew := (E.old_surgery_times _ (htime s hs)).mpr hT
    have htnew : a + t / q ∈ Ico (E.extended.event (a + s / q) hTnew).tMinus
        (a + s / q) := by
      simpa only [E.old_event_reference _ hT hTnew] using ht'
    let y := ((F.event _ hT).pre_identify ⟨_, ht'⟩).symm
      ((f t ht).symm (d.forward t ht x))
    have hy : y ∈ (F.event _ hT).retained_pre := by
      have hmem := d.pre_retained_at_surgery s hs hTnew t ht htnew x hx
      rw [← E.eventPreEquivalence_interior hT hTnew ⟨_, ht'⟩ (htime t ht) htnew] at hmem
      rcases hmem with ⟨z, hz, heq⟩
      have hzy : z = y := by
        apply (E.eventPreEquivalence hT hTnew ⟨_, ht'⟩ (htime t ht) htnew).injective
        change E.eventPreEquivalence hT hTnew ⟨_, ht'⟩ (htime t ht) htnew z =
          E.eventPreEquivalence hT hTnew ⟨_, ht'⟩ (htime t ht) htnew y
        simpa only [eventPreEquivalence_apply, y, f, Diffeomorph.apply_symm_apply] using heq
      exact hzy ▸ interior_subset hz
    apply (f s hs).injective
    have hret := E.old_retention _ hT hTnew ⟨_, ht'⟩ (htime t ht) htnew y hy
    change (f s hs) ((F.event _ hT).retention.map y) =
      (f s hs) ((f s hs).symm (d.forward s hs x))
    simpa only [y, f, Diffeomorph.apply_symm_apply,
      d.surgery_compatibility s hs hTnew t ht htnew x hx] using hret

theorem pullCylinder_forward (d : SurgeryFlowCylinder E.extended C a q J U)
    (htime : ∀ s ∈ J, a + s / q ∈ F.time_domain)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (E.pullCylinder d htime).forward s hs x =
      (E.identify (a + s / q) (htime s hs)).symm (d.forward s hs x) := rfl

end PoincareConjecture.SurgeryFlowExtension
