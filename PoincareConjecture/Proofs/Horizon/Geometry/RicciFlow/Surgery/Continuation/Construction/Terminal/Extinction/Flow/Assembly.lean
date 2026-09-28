import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Events
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Maximality
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Coherence









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Extinction

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)

def event (U : ℝ) (hU : U ∈ Splice.eventTimes F T)
    [Nonempty (slice F T U).carrier] :
    SurgeryEventData F.standard_initial F.local_constants F.parameters
      (slice F T) (metric F T) U := by
  have hold := event_time_old U hU
  let := I.slices_nonempty U (F.surgery_times_subset hold)
  exact Splice.oldEvent F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T)
    U hold (I.time_domain_eq ▸ F.surgery_times_subset hold).2

def vanishingEvent (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
    (U : ℝ) (hU : U ∈ Splice.eventTimes F T) [IsEmpty (slice F T U).carrier] :
    SurgeryVanishingEventData F.parameters (slice F T) (metric F T) U := by
  have heq := vanishing_time_eq I U hU
  subst U
  exact Splice.vanishingEvent F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) V

def flow (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
    (hV : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
      ∀ hs' : s ∈ Ico V.tMinus T, ∀ ht' : t ∈ Ico V.tMinus T, ∀ x,
        (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
          (V.pre_identify ⟨s, hs'⟩ x) = V.pre_identify ⟨t, ht'⟩ x) :
    SurgeryFlowData.{u} where
  standard_initial := F.standard_initial
  local_constants := F.local_constants
  parameters := F.parameters
  time_domain := {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < ⊤}
  time_domain_interval := ⟨fun _ ha _ _ _ hx =>
    ⟨ha.1.trans hx.1, ENNReal.ofReal_lt_top⟩⟩
  time_domain_nonnegative := fun _ h => h.1
  zero_mem := ⟨le_rfl, ENNReal.ofReal_lt_top⟩
  slice := slice F T
  metric := metric F T
  connection := connection (F := F) (T := T)
  slices_compact := fun t ht => slices_compact I t ht.1
  no_two_sided_projective_plane := fun t ht => no_two_sided_projective_plane I t ht.1
  initial_nonempty := initial_nonempty I
  initial_normalized := initial_normalized I
  surgery_times := Splice.eventTimes F T
  surgery_times_subset := by
    intro t ht
    rcases mem_insert_iff.mp ht with hEq | hold
    · exact ⟨hEq ▸ I.terminal_pos.le, ENNReal.ofReal_lt_top⟩
    · exact ⟨F.time_domain_nonnegative (F.surgery_times_subset hold), ENNReal.ofReal_lt_top⟩
  zero_not_surgery := by
    simp only [Splice.eventTimes, mem_insert_iff, not_or]
    exact ⟨I.terminal_pos.ne, F.zero_not_surgery⟩
  surgery_times_locally_finite := fun t _ =>
    ⟨1, by norm_num, ((surgery_times_finite I).insert T).subset inter_subset_left⟩
  regular_slabs := fun _ _ hab hJ hfree =>
    Splice.regularSlab F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T)
      I.time_domain_eq hab hJ hfree
  slab_transport_coherent := Splice.regularSlab_transport_coherent F T
    (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) I.time_domain_eq
  event := event I
  vanishing_event := vanishingEvent I V
  event_slab_compatibility := by
    intro U hU hne a b hab hJ hfree s t hs ht hs' ht' x
    have hold := event_time_old U hU
    let := I.slices_nonempty U (F.surgery_times_subset hold)
    exact Splice.oldEvent_slab_compatibility F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) I.time_domain_eq U hold
      (I.time_domain_eq ▸ F.surgery_times_subset hold).2
      a b hab hJ hfree s t hs ht hs' ht' x
  vanishing_slab_compatibility := by
    intro U hU he a b hab hJ hfree s t hs ht hs' ht' x
    have heq := vanishing_time_eq I U hU
    subst U
    exact Splice.vanishingEvent_slab_compatibility F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) I.time_domain_eq V hV
      a b hab hJ hfree s t hs ht hs' ht' x
  maximal_intervals := by
    intro a b ha hstart hab _hJ hfree _hne hend
    have hb : b ∈ F.surgery_times ∨ b = T := by
      rcases hend with hevent | hout
      · exact (mem_insert_iff.mp hevent).symm
      · exact (hout ⟨ha.1.trans hab.le, ENNReal.ofReal_lt_top⟩).elim
    exact Splice.maximal_intervals_before F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) I a b ha.1 hstart hab hfree hb
  extinction_permanent := fun s t hs _ht hst he =>
    extinction_permanent F T I s t hs.1 hst he

end PoincareConjecture.Surgery.Extinction
