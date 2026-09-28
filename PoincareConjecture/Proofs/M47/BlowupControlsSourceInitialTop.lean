import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRetention
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_retained_top
    {F : SurgeryFlowData.{u}} {T : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    (old : SurgeryTerminalStrongNeck F T hT i)
    (U : Set (F.event T hT).terminal.carrier) (hU : IsOpen U)
    (hnegative : U ⊆ ((F.event T hT).necks i).neck.region
      (-((F.event T hT).necks i).neck.epsilon⁻¹) 0) :
    ∃ E : SurgeryFlowCylinder F (F.event T hT).terminal T
        (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Ioc (-1 : ℝ) 0) U,
      (∀ s (hs : s ∈ Ioo (-1 : ℝ) 0) (hs' : s ∈ Ioc (-1 : ℝ) 0) x,
        E.forward s hs' x = old.cylinder.forward s hs x) ∧
      ∀ hs x, HEq (E.forward 0 hs x)
        ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x)) := by
  classical
  let event := F.event T hT
  let q := (event.necks i).neck.scale⁻¹ ^ 2
  let e := old.cylinder.restrict Subset.rfl ordConnected_Ioo
    (fun x hx => (hnegative hx).1)
  let top := (M44.regionEquivalenceInteriorChart event.limit_identify).symm.trans
    (M44.regionEquivalenceInteriorChart event.retention)
  have htop (x : event.terminal.carrier) (hx : x ∈ U) : x ∈ top.source := by
    change x ∈ interior (univ : Set event.terminal.carrier) ∧
      event.limit_identify.inverse x ∈ interior event.retained_pre
    exact ⟨by simp, source_negative_neck_interior_retained hT i (hnegative hx)⟩
  have htopPost (x : event.terminal.carrier) (hx : x ∈ U) :
      top x ∈ interior event.retained_post :=
    (M44.regionEquivalenceInteriorChart event.retention).map_source
      (source_negative_neck_interior_retained hT i (hnegative hx))
  let castTop (t : ℝ) (ht : T = t) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) event.terminal.carrier (F.slice t).carrier ∞ :=
    Eq.ndrec (motive := fun r => PartialDiffeomorph (𝓡 3) (𝓡 3)
      event.terminal.carrier (F.slice r).carrier ∞) top ht
  have hcastSource (t : ℝ) (ht : T = t) : (castTop t ht).source = top.source := by
    cases ht
    rfl
  have hcastPoint (t : ℝ) (ht : T = t) (x : event.terminal.carrier) :
      HEq (castTop t ht x) (top x) := by
    cases ht
    rfl
  have hcastPost (t : ℝ) (ht : T = t) (hS : t ∈ F.surgery_times)
      [Nonempty (F.slice t).carrier] (x : event.terminal.carrier) (hx : x ∈ U) :
      castTop t ht x ∈ interior (F.event t hS).retained_post := by
    cases ht
    exact htopPost x hx
  let chart (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) event.terminal.carrier
        (F.slice (T + s / q)).carrier ∞ :=
    if hs0 : s = 0 then
      castTop (T + s / q) (by rw [hs0, zero_div, add_zero])
    else M44.cylinderSliceChart e hU s ⟨hs.1, lt_of_le_of_ne hs.2 hs0⟩
  have hsource (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) : U ⊆ (chart s hs).source := by
    by_cases hs0 : s = 0
    · subst s
      dsimp only [chart]
      rw [dif_pos rfl, hcastSource]
      exact htop
    · dsimp only [chart]
      rw [dif_neg hs0]
      exact Subset.refl U
  have hold (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) (hs0 : s < 0)
      (x : event.terminal.carrier) : chart s hs x = old.cylinder.forward s ⟨hs.1, hs0⟩ x := by
    dsimp only [chart]
    rw [dif_neg hs0.ne]
    rfl
  have hclock : StrictMono (fun s : ℝ => T + s / q) := by
    intro s t hst
    simpa only [add_comm] using
      add_lt_add_left ((div_lt_div_iff_of_pos_right old.cylinder.scale_pos).mpr hst) T
  have hpre (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
      (ht : T + s / q ∈ Ico event.tMinus T) (x : event.terminal.carrier) (hx : x ∈ U) :
      (event.pre_identify ⟨T + s / q, ht⟩).symm (old.cylinder.forward s hs x) =
        event.limit_identify.inverse x := by
    rw [old.reference_compatibility s hs ht x (hnegative hx).1]
    exact (event.pre_identify _).symm_apply_apply _
  have hcastPre (t0 : ℝ) (ht0 : T = t0) (hS : t0 ∈ F.surgery_times)
      [Nonempty (F.slice t0).carrier] (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
      (ht : T + s / q ∈ Ico (F.event t0 hS).tMinus t0)
      (x : event.terminal.carrier) (hx : x ∈ U) :
      ((F.event t0 hS).pre_identify ⟨T + s / q, ht⟩).symm
        (old.cylinder.forward s hs x) ∈ interior (F.event t0 hS).retained_pre := by
    cases ht0
    rw [hpre s hs ht x hx]
    exact source_negative_neck_interior_retained hT i (hnegative hx)
  have hcastRetention (t0 : ℝ) (ht0 : T = t0) (hS : t0 ∈ F.surgery_times)
      [Nonempty (F.slice t0).carrier] (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
      (ht : T + s / q ∈ Ico (F.event t0 hS).tMinus t0)
      (x : event.terminal.carrier) (hx : x ∈ U) :
      (F.event t0 hS).retention.map
        (((F.event t0 hS).pre_identify ⟨T + s / q, ht⟩).symm
          (old.cylinder.forward s hs x)) = castTop t0 ht0 x := by
    cases ht0
    rw [hpre s hs ht x hx]
    rfl
  let E : SurgeryFlowCylinder F event.terminal T q (Ioc (-1 : ℝ) 0) U := {
    scale_pos := old.cylinder.scale_pos
    interval_connected := ordConnected_Ioc
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      rcases lt_or_eq_of_le hs.2 with hs0 | rfl
      · exact old.cylinder.time_subset (mem_image_of_mem _ ⟨hs.1, hs0⟩)
      · simpa only [zero_div, add_zero] using F.surgery_times_subset hT
    forward := fun s hs => chart s hs
    inverse := fun s hs => (chart s hs).symm
    forward_smooth := fun s hs => (chart s hs).contMDiffOn.mono (hsource s hs)
    inverse_smooth := by
      intro s hs
      apply (chart s hs).contMDiffOn_invFun.mono
      rintro _ ⟨x, hx, rfl⟩
      exact (chart s hs).map_source (hsource s hs hx)
    left_inverse := fun s hs x hx => (chart s hs).left_inv (hsource s hs hx)
    right_inverse := by
      rintro s hs _ ⟨x, hx, rfl⟩
      exact (chart s hs).right_inv ((chart s hs).map_source (hsource s hs hx))
    slab_compatibility := by
      intro l r hlr hJ hfree s hs t ht hs' ht' x hx
      rcases lt_or_eq_of_le hs.2 with hs0 | rfl
      · rcases lt_or_eq_of_le ht.2 with ht0 | rfl
        · rw [hold s hs hs0 x, hold t ht ht0 x]
          exact old.cylinder.slab_compatibility l r hlr hJ hfree
            s ⟨hs.1, hs0⟩ t ⟨ht.1, ht0⟩ hs' ht' x (hnegative hx).1
        · have hS : T + 0 / q ∈ F.surgery_times := by simpa only [zero_div, add_zero] using hT
          exact (Set.disjoint_left.mp hfree hS
            ⟨hs'.1.trans_lt (hclock hs0), ht'.2⟩).elim
      · rcases lt_or_eq_of_le ht.2 with ht0 | rfl
        · have hS : T + 0 / q ∈ F.surgery_times := by simpa only [zero_div, add_zero] using hT
          exact (Set.disjoint_left.mp hfree hS
            ⟨ht'.1.trans_lt (hclock ht0), hs'.2⟩).elim
        · exact SurgeryRegularSlab.transport_self _ _ _
    retained_at_surgery := by
      intro s hs hS _ hearlier
      rintro _ ⟨x, hx, rfl⟩
      rcases lt_or_eq_of_le hs.2 with hs0 | rfl
      · rw [hold s hs hs0 x]
        obtain ⟨t, ht, hts⟩ := hearlier
        exact old.cylinder.retained_at_surgery s ⟨hs.1, hs0⟩ hS
          ⟨t, ⟨ht.1, hts.trans hs0⟩, hts⟩ (mem_image_of_mem _ (hnegative hx).1)
      · dsimp only [chart]
        rw [dif_pos rfl]
        exact hcastPost _ _ hS x hx
    pre_retained_at_surgery := by
      intro s hs hS _ t ht ht' x hx
      have hts : t < s := hclock.lt_iff_lt.mp ht'.2
      rcases lt_or_eq_of_le hs.2 with hs0 | rfl
      · rw [hold t ht (hts.trans hs0) x]
        exact old.cylinder.pre_retained_at_surgery s ⟨hs.1, hs0⟩ hS
          t ⟨ht.1, hts.trans hs0⟩ ht' x (hnegative hx).1
      · rw [hold t ht hts x]
        exact hcastPre _ (by rw [zero_div, add_zero]) hS t ⟨ht.1, hts⟩ ht' x hx
    surgery_compatibility := by
      intro s hs hS _ t ht ht' x hx
      have hts : t < s := hclock.lt_iff_lt.mp ht'.2
      rcases lt_or_eq_of_le hs.2 with hs0 | rfl
      · rw [hold t ht (hts.trans hs0) x, hold s hs hs0 x]
        exact old.cylinder.surgery_compatibility s ⟨hs.1, hs0⟩ hS
          t ⟨ht.1, hts.trans hs0⟩ ht' x (hnegative hx).1
      · rw [hold t ht hts x]
        dsimp only [chart]
        rw [dif_pos rfl]
        exact hcastRetention _ _ hS t ⟨ht.1, hts⟩ ht' x hx
  }
  refine ⟨E, fun s hs hs' x => hold s hs' hs.2 x, ?_⟩
  intro hs x
  change HEq (chart 0 hs x) (top x)
  dsimp only [chart]
  rw [dif_pos rfl]
  exact hcastPoint _ _ x

end PoincareConjecture.M47
