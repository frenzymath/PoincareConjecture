import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.StrongBoundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.CanonicalTail

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Extinction

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
  (hV : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico V.tMinus T, ∀ ht' : t ∈ Ico V.tMinus T, ∀ x,
      (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        (V.pre_identify ⟨s, hs'⟩ x) = V.pre_identify ⟨t, ht'⟩ x)

theorem admissible : SurgeryFlowAdmissible (flow I (canonicalVanishingEvent I V) hV) := by
  let V' := canonicalVanishingEvent I V
  let E := extension I V' hV
  constructor
  · intro U hU hne i
    let : Nonempty (slice F T U).carrier := hne
    have hold := event_time_old U hU
    let := I.slices_nonempty U (F.surgery_times_subset hold)
    obtain ⟨N⟩ := I.admissible.strong_boundaries U hold i
    exact ⟨strongBoundary I V' hV U hold hU i N⟩
  · intro U hU hne t ht x hx
    let : Nonempty (slice F T U).carrier := hne
    have hold := event_time_old U hU
    let := I.slices_nonempty U (F.surgery_times_subset hold)
    have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hold).2
    have htF : t.1 ∈ F.time_domain := I.time_domain_eq ▸
      (show t.1 ∈ Ico 0 T from
        ⟨(F.event U hold).tMinus_nonnegative.trans t.2.1, t.2.2.trans hUT⟩)
    let e := Splice.identifyBefore F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T)
      (F.event U hold).tMinus ((F.event U hold).tMinus_lt.trans hUT)
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∉ interior (F.event U hold).retained_pre := by
      intro hy
      apply hx
      change e y ∈ interior (Splice.oldEvent F T (emptyCarrier (F.slice 0))
        (emptyFlow (F.metric 0) T) U hold hUT).retained_pre
      rw [← Splice.oldEvent_retained_pre_image F T (emptyCarrier (F.slice 0))
        (emptyFlow (F.metric 0) T) U hold hUT]
      change e.toHomeomorph y ∈ interior (e.toHomeomorph '' (F.event U hold).retained_pre)
      rw [← e.toHomeomorph.image_interior]
      exact ⟨y, hy, rfl⟩
    have hc := E.canonical_control_direct t.1 htF ((F.event U hold).pre_identify t y)
      F.parameters.epsilon F.parameters.C
      (I.admissible.strong_disappearing U hold t ht y hy)
    have hp := Splice.oldEvent_pre_identify F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hold hUT t y
    exact hp.symm ▸ hc
  · intro U hU he t ht x
    let : IsEmpty (slice F T U).carrier := he
    have hEq := vanishing_time_eq I U hU
    subst U
    obtain ⟨y, rfl⟩ := (Splice.identifyBefore F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) V'.tMinus V'.tMinus_lt).surjective x
    have htF : t.1 ∈ F.time_domain := I.time_domain_eq ▸
      (show t.1 ∈ Ico 0 T from ⟨V'.tMinus_nonnegative.trans t.2.1, t.2.2⟩)
    have hc := E.canonical_control_direct t.1 htF (V'.pre_identify t y)
      F.parameters.epsilon F.parameters.C (canonicalVanishingEvent_control I V t ht y)
    have hp := Splice.vanishingEvent_pre_identify F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) V' t y
    exact hp.symm ▸ hc

end PoincareConjecture.Surgery.Extinction
