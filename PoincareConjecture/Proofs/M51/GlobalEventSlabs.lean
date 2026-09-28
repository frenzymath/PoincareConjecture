import PoincareConjecture.Proofs.M51.GlobalVanishingEvents
import PoincareConjecture.Proofs.M51.GlobalSlabs











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F0 k)

private theorem globalSlab_preidentify_compatible
    (n : ℕ) (r T : ℝ) (hpre : Ico r T ⊆ (Q.flow n).time_domain)
    (J : ∀ t : Ico r T, ((Q.flow n).slice r).carrier →
      ((Q.flow n).slice t.1).carrier)
    (hcompat : ∀ a b hab hK hfree,
      ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
      ∀ hs' : s ∈ Ico r T, ∀ ht' : t ∈ Ico r T, ∀ x,
        ((Q.flow n).regular_slabs a b hab hK hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
          (J ⟨s, hs'⟩ x) = J ⟨t, ht'⟩ x)
    (a b : ℝ) (hab : a < b) (hK : Icc a b ⊆ Ici 0)
    (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico r T) (ht' : t ∈ Ico r T)
    (x : ((Q.flow n).slice r).carrier) :
    (Q.globalSlab a b hab hK hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      (Q.globalIdentify n s (hpre hs') (J ⟨s, hs'⟩ x)) =
        Q.globalIdentify n t (hpre ht') (J ⟨t, ht'⟩ x) := by
  by_cases hst : s = t
  · subst t
    simp only [SurgeryRegularSlab.transport, Diffeomorph.apply_symm_apply]
  · have hcd : min s t < max s t := by
      rcases lt_or_gt_of_ne hst with h | h
      · simpa only [min_eq_left h.le, max_eq_right h.le] using h
      · simpa only [min_eq_right h.le, max_eq_left h.le] using h
    have hsK : s ∈ Icc (min s t) (max s t) := ⟨min_le_left _ _, le_max_left _ _⟩
    have htK : t ∈ Icc (min s t) (max s t) := ⟨min_le_right _ _, le_max_right _ _⟩
    have hKsource : Icc (min s t) (max s t) ⊆ (Q.flow n).time_domain := by
      intro u hu
      exact hpre ⟨(le_min hs'.1 ht'.1).trans hu.1,
        hu.2.trans_lt (max_lt_iff.mpr ⟨hs'.2, ht'.2⟩)⟩
    have hsub : Ioc (min s t) (max s t) ⊆ Ioc a b := by
      intro u hu
      exact ⟨(le_min hs.1 ht.1).trans_lt hu.1, hu.2.trans (max_le hs.2 ht.2)⟩
    have hfreeSmall : Disjoint Q.globalSurgeryTimes (Ioc (min s t) (max s t)) :=
      hfree.mono_right hsub
    have hfreeSource := Q.stage_surgeryFree_of_global n hfreeSmall
    calc
      _ = Q.globalIdentify n t (hKsource htK)
          (((Q.flow n).regular_slabs (min s t) (max s t) hcd hKsource
            hfreeSource).transport ⟨s, hsK⟩ ⟨t, htK⟩ (J ⟨s, hs'⟩ x)) :=
        Q.globalSlab_compare a b hab hK hfree n (min s t) (max s t) hcd
          hKsource hfreeSource s t hs ht hsK htK (J ⟨s, hs'⟩ x)
      _ = _ := congrArg (Q.globalIdentify n t (hKsource htK))
        (hcompat (min s t) (max s t) hcd hKsource hfreeSource s t hsK htK hs' ht' x)



theorem globalEvent_slab_compatibility
    (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) [Nonempty (Q.globalSlice T).carrier]
    (a b : ℝ) (hab : a < b) (hK : Icc a b ⊆ Ici 0)
    (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico (Q.globalEvent T hT).tMinus T)
    (ht' : t ∈ Ico (Q.globalEvent T hT).tMinus T)
    (x : (Q.globalSlice (Q.globalEvent T hT).tMinus).carrier) :
    (Q.globalSlab a b hab hK hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      ((Q.globalEvent T hT).pre_identify ⟨s, hs'⟩ x) =
        (Q.globalEvent T hT).pre_identify ⟨t, ht'⟩ x := by
  rw [Q.globalEvent_pre_identify, Q.globalEvent_pre_identify]
  let := Q.eventStageNonempty T hT
  exact Q.globalSlab_preidentify_compatible (Q.representativeIndex T)
    (Q.globalEventSource T hT).tMinus T
    (fun u hu => Q.globalEventPreTime T hT ⟨u, hu⟩)
    (fun t => (Q.globalEventSource T hT).pre_identify t)
    ((Q.flow (Q.representativeIndex T)).event_slab_compatibility T
      (Q.eventStageSurgery T hT))
    a b hab hK hfree s t hs ht hs' ht' ((Q.globalEventInitialMap T hT).symm x)



theorem globalVanishingEvent_slab_compatibility
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) [IsEmpty (Q.globalSlice T).carrier]
    (a b : ℝ) (hab : a < b) (hK : Icc a b ⊆ Ici 0)
    (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico (Q.globalVanishingEvent m13 T hT).tMinus T)
    (ht' : t ∈ Ico (Q.globalVanishingEvent m13 T hT).tMinus T)
    (x : (Q.globalSlice (Q.globalVanishingEvent m13 T hT).tMinus).carrier) :
    (Q.globalSlab a b hab hK hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      ((Q.globalVanishingEvent m13 T hT).pre_identify ⟨s, hs'⟩ x) =
        (Q.globalVanishingEvent m13 T hT).pre_identify ⟨t, ht'⟩ x := by
  rw [Q.globalVanishingEvent_pre_identify, Q.globalVanishingEvent_pre_identify]
  let := Q.eventStageIsEmpty T hT
  exact Q.globalSlab_preidentify_compatible (Q.representativeIndex T)
    (Q.globalVanishingSource T hT).tMinus T
    (fun u hu => Q.globalVanishingPreTime T hT ⟨u, hu⟩)
    (fun t => (Q.globalVanishingSource T hT).pre_identify t)
    ((Q.flow (Q.representativeIndex T)).vanishing_slab_compatibility T
      (Q.eventStageSurgery T hT))
    a b hab hK hfree s t hs ht hs' ht' ((Q.globalVanishingInitialMap T hT).symm x)

end PoincareConjecture.M51.CompletedStageChain
