import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.StrongBoundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Properties

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
  [Nonempty C.carrier] (hC : IsCompact (univ : Set C.carrier))
  (hRP : SurgeryNoTwoSidedProjectivePlane C) (hB : ENNReal.ofReal T < B)
  (hblow : B ≠ ⊤ → ∀ L s : ℝ, s < B.toReal →
    ∃ t ∈ Ioo (max T s) B.toReal, ∃ x : C.carrier,
      L < (R.connection t).curvatureTensorNorm x)
  (hE : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico E.tMinus T, ∀ ht' : t ∈ Ico E.tMinus T, ∀ x,
      (Splice.regularSlab F T C R I.time_domain_eq hab hJ hfree).transport
        ⟨s, hs⟩ ⟨t, ht⟩ (E.pre_identify ⟨s, hs'⟩ x) = E.pre_identify ⟨t, ht'⟩ x)

theorem old_strong_disappearing (U : ℝ) (hU : U ∈ F.surgery_times)
    (hU' : U ∈ (flow I C R E hC hRP hB hblow hE).surgery_times)
    [Nonempty ((flow I C R E hC hRP hB hblow hE).slice U).carrier] :
    ∀ t : Ico ((flow I C R E hC hRP hB hblow hE).event U hU').tMinus U,
      ((flow I C R E hC hRP hB hblow hE).event U hU').disappearing_start ≤ t.1 →
      ∀ x, x ∉ interior ((flow I C R E hC hRP hB hblow hE).event U hU').retained_pre →
        SurgeryCanonicalControl (flow I C R E hC hRP hB hblow hE) t.1
          (((flow I C R E hC hRP hB hblow hE).event U hU').pre_identify t x)
          F.parameters.epsilon F.parameters.C := by
  let := I.slices_nonempty U (F.surgery_times_subset hU)
  have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  change ∀ t : Ico (event I C R E U hU').tMinus U,
    (event I C R E U hU').disappearing_start ≤ t.1 →
    ∀ x, x ∉ interior (event I C R E U hU').retained_pre →
      SurgeryCanonicalControl (flow I C R E hC hRP hB hblow hE) t.1
        ((event I C R E U hU').pre_identify t x) F.parameters.epsilon F.parameters.C
  rw [event_old I C R E U hU hU']
  intro t ht x hx
  let A := extension I C R E hC hRP hB hblow hE
  have htF : t.1 ∈ F.time_domain := by
    exact I.time_domain_eq.symm.subset
      ⟨(F.event U hU).tMinus_nonnegative.trans t.2.1, t.2.2.trans hUT⟩
  let e := Splice.identifyBefore F T C R
    (F.event U hU).tMinus ((F.event U hU).tMinus_lt.trans hUT)
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : y ∉ interior (F.event U hU).retained_pre := by
    intro hy
    apply hx
    change e y ∈ interior (Splice.oldEvent F T C R U hU hUT).retained_pre
    rw [← Splice.oldEvent_retained_pre_image F T C R U hU hUT]
    change e.toHomeomorph y ∈ interior (e.toHomeomorph '' (F.event U hU).retained_pre)
    rw [← e.toHomeomorph.image_interior]
    exact ⟨y, hy, rfl⟩
  have hc := A.canonical_control_direct t.1 htF ((F.event U hU).pre_identify t y)
    F.parameters.epsilon F.parameters.C
    (I.admissible.strong_disappearing U hU t ht y hy)
  exact (Splice.oldEvent_pre_identify F T C R U hU hUT t y).symm ▸ hc

theorem admissible_of_terminal
    [Nonempty ((flow I C R E hC hRP hB hblow hE).slice T).carrier]
    (hboundaries : ∀ i, Nonempty (SurgeryTerminalStrongNeck
      (flow I C R E hC hRP hB hblow hE) T
      (surgery_at_terminal I C R E hC hRP hB hblow hE) i))
    (hdisappearing : ∀ t : Ico E.tMinus T, E.disappearing_start ≤ t.1 →
      ∀ x, x ∉ interior E.retained_pre →
        SurgeryCanonicalControl (flow I C R E hC hRP hB hblow hE) t.1
          (E.pre_identify t x) F.parameters.epsilon F.parameters.C) :
    SurgeryFlowAdmissible (flow I C R E hC hRP hB hblow hE) := by
  constructor
  · intro U hU hne
    by_cases heq : U = T
    · subst U
      exact hboundaries
    · exact old_strong_boundaries I C R E hC hRP hB hblow hE U
        ((mem_insert_iff.mp hU).resolve_left heq) hU
  · intro U hU hne
    by_cases heq : U = T
    · subst U
      change ∀ t : Ico (event I C R E T hU).tMinus T,
        (event I C R E T hU).disappearing_start ≤ t.1 →
        ∀ x, x ∉ interior (event I C R E T hU).retained_pre →
          SurgeryCanonicalControl (flow I C R E hC hRP hB hblow hE) t.1
            ((event I C R E T hU).pre_identify t x) F.parameters.epsilon F.parameters.C
      rw [event_terminal I C R E hU]
      exact hdisappearing
    · exact old_strong_disappearing I C R E hC hRP hB hblow hE U
        ((mem_insert_iff.mp hU).resolve_left heq) hU
  · intro U hU he
    let : IsEmpty (Splice.slice F T C R U).carrier := he
    obtain ⟨x⟩ := slices_nonempty I C R U (event_nonnegative I U hU)
    exact isEmptyElim x

end PoincareConjecture.Surgery.TerminalRestart
