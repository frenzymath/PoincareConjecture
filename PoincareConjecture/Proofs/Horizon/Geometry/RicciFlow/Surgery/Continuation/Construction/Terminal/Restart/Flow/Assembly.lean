import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Maximality
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Events







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})
  (E : SurgeryEventData F.standard_initial F.local_constants F.parameters
    (Splice.slice F T C R) (Splice.metric F T C R) T)

def event (U : ℝ) (hU : U ∈ Splice.eventTimes F T) :
    SurgeryEventData F.standard_initial F.local_constants F.parameters
      (Splice.slice F T C R) (Splice.metric F T C R) U := by
  by_cases heq : U = T
  · subst U
    exact E
  · have hold : U ∈ F.surgery_times := (mem_insert_iff.mp hU).resolve_left heq
    let := I.slices_nonempty U (F.surgery_times_subset hold)
    exact Splice.oldEvent F T C R U hold (I.time_domain_eq ▸ F.surgery_times_subset hold).2

@[simp] theorem event_terminal (hT : T ∈ Splice.eventTimes F T) :
    event I C R E T hT = E := by
  simp [event]

theorem event_old (U : ℝ) (hU : U ∈ F.surgery_times)
    (hU' : U ∈ Splice.eventTimes F T) [Nonempty (F.slice U).carrier] :
    event I C R E U hU' =
      Splice.oldEvent F T C R U hU (I.time_domain_eq ▸ F.surgery_times_subset hU).2 := by
  simp [event, (I.time_domain_eq ▸ F.surgery_times_subset hU).2.ne]

include I in
theorem event_nonnegative (U : ℝ) (hU : U ∈ Splice.eventTimes F T) : 0 ≤ U := by
  rcases mem_insert_iff.mp hU with rfl | hold
  · exact I.terminal_pos.le
  · exact F.time_domain_nonnegative (F.surgery_times_subset hold)

variable [Nonempty C.carrier]

def flow (hC : IsCompact (univ : Set C.carrier))
    (hRP : SurgeryNoTwoSidedProjectivePlane C) (hB : ENNReal.ofReal T < B)
    (hblow : B ≠ ⊤ → ∀ L s : ℝ, s < B.toReal →
      ∃ t ∈ Ioo (max T s) B.toReal, ∃ x : C.carrier,
        L < (R.connection t).curvatureTensorNorm x)
    (hE : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
      ∀ hs' : s ∈ Ico E.tMinus T, ∀ ht' : t ∈ Ico E.tMinus T, ∀ x,
        (Splice.regularSlab F T C R I.time_domain_eq hab hJ hfree).transport
          ⟨s, hs⟩ ⟨t, ht⟩ (E.pre_identify ⟨s, hs'⟩ x) = E.pre_identify ⟨t, ht'⟩ x) :
    SurgeryFlowData.{u} where
  standard_initial := F.standard_initial
  local_constants := F.local_constants
  parameters := F.parameters
  time_domain := {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B}
  time_domain_interval := ⟨fun _ ha _ hb _ hx =>
    ⟨ha.1.trans hx.1, (ENNReal.ofReal_le_ofReal hx.2).trans_lt hb.2⟩⟩
  time_domain_nonnegative := fun _ ht => ht.1
  zero_mem := ⟨le_rfl, (ENNReal.ofReal_le_ofReal I.terminal_pos.le).trans_lt hB⟩
  slice := Splice.slice F T C R
  metric := Splice.metric F T C R
  connection := Splice.connection F T C R
  slices_compact := fun t ht => slices_compact I C R hC t ht.1
  no_two_sided_projective_plane := fun t ht => no_two_sided_projective_plane I C R hRP t ht.1
  initial_nonempty := slices_nonempty I C R 0 le_rfl
  initial_normalized := initial_normalized I C R
  surgery_times := Splice.eventTimes F T
  surgery_times_subset := by
    intro t ht
    rcases mem_insert_iff.mp ht with rfl | hold
    · exact ⟨I.terminal_pos.le, hB⟩
    · exact old_times I hB (F.surgery_times_subset hold)
  zero_not_surgery := by
    simp only [Splice.eventTimes, mem_insert_iff, not_or]
    exact ⟨I.terminal_pos.ne, F.zero_not_surgery⟩
  surgery_times_locally_finite := fun _ _ =>
    ⟨1, by norm_num, ((Extinction.surgery_times_finite I).insert T).subset inter_subset_left⟩
  regular_slabs := fun _ _ hab hJ hfree => Splice.regularSlab F T C R I.time_domain_eq hab hJ hfree
  slab_transport_coherent := Splice.regularSlab_transport_coherent F T C R I.time_domain_eq
  event := fun U hU _ => event I C R E U hU
  vanishing_event := by
    intro U hU he
    exact isEmptyElim (Classical.choice (slices_nonempty I C R U (event_nonnegative I U hU)))
  event_slab_compatibility := by
    intro U hU hne
    by_cases heq : U = T
    · subst U
      rw [event_terminal I C R E hU]
      exact hE
    · have hold : U ∈ F.surgery_times := (mem_insert_iff.mp hU).resolve_left heq
      let := I.slices_nonempty U (F.surgery_times_subset hold)
      rw [event_old I C R E U hold hU]
      exact Splice.oldEvent_slab_compatibility F T C R I.time_domain_eq U hold
        (I.time_domain_eq ▸ F.surgery_times_subset hold).2
  vanishing_slab_compatibility := by
    intro U hU he
    obtain ⟨x⟩ := slices_nonempty I C R U (event_nonnegative I U hU)
    exact isEmptyElim x
  maximal_intervals := by
    intro a b ha hstart hab hJ hfree _hne hend
    exact maximal_intervals I C R hB hblow a b ha hstart hab hJ hfree hend
  extinction_permanent := by
    intro s _t hs _ht _hst he
    let := he
    obtain ⟨x⟩ := slices_nonempty I C R s hs.1
    exact isEmptyElim x

end PoincareConjecture.Surgery.TerminalRestart
