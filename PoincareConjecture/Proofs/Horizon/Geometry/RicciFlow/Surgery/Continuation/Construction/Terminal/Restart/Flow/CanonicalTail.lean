import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.CanonicalTail
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Admissible








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

theorem canonicalNonemptyEvent_restart_control (t : Ico E.tMinus T)
    (ht : (canonicalNonemptyEvent I C R E).disappearing_start ≤ t.1)
    (x : (Splice.slice F T C R E.tMinus).carrier) (hx : x ∉ interior E.retained_pre) :
    SurgeryCanonicalControl
      (flow I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE) t.1
      (E.pre_identify t x) F.parameters.epsilon F.parameters.C := by
  let A := extension I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE
  have htF : t.1 ∈ F.time_domain := I.time_domain_eq.symm.subset
    ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2⟩
  let e := Splice.identifyBefore F T C R t.1 t.2.2
  have hc := A.canonical_control_direct t.1 htF (e.symm (E.pre_identify t x))
    F.parameters.epsilon F.parameters.C (canonicalNonemptyEvent_control I C R E t ht x hx)
  have hid : A.identify t.1 htF (e.symm (E.pre_identify t x)) = E.pre_identify t x :=
    e.apply_symm_apply _
  exact hid ▸ hc

local instance canonical_terminal_nonempty :
    Nonempty ((flow I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE).slice T).carrier :=
  slices_nonempty I C R T I.terminal_pos.le

theorem admissible_from_terminal_boundaries
    (hboundaries : ∀ i, Nonempty (SurgeryTerminalStrongNeck
      (flow I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE) T
      (surgery_at_terminal I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE) i)) :
    SurgeryFlowAdmissible
      (flow I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE) :=
  admissible_of_terminal I C R (canonicalNonemptyEvent I C R E) hC hRP hB hblow hE
    hboundaries (canonicalNonemptyEvent_restart_control I C R E hC hRP hB hblow hE)

end PoincareConjecture.Surgery.TerminalRestart
