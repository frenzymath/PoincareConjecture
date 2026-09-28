import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants









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

include I

theorem exists_event_canonical_tail : ∃ s : ℝ, E.disappearing_start ≤ s ∧ s < T ∧
    ∀ t : Ico E.tMinus T, s ≤ t.1 → ∀ x : (Splice.slice F T C R E.tMinus).carrier,
      x ∉ interior E.retained_pre →
      SurgeryCanonicalControl F t.1
        ((Splice.identifyBefore F T C R t.1 t.2.2).symm (E.pre_identify t x))
        F.parameters.epsilon F.parameters.C := by
  have hrT : 0 < F.parameters.r T := F.parameters.r_pos T I.terminal_pos.le
  have hinv : (F.parameters.r T)⁻¹ < I.rho⁻¹ :=
    (inv_lt_inv₀ hrT I.rho_pos).mpr I.rho_lt_r
  have hlevel : (F.parameters.r T)⁻¹ ^ 2 < (F.parameters.delta T * F.parameters.r T)⁻¹ ^ 2 := by
    rw [← I.rho_eq]
    have := inv_pos.mpr hrT
    nlinarith
  obtain ⟨s, _hs, hsT, htail⟩ := E.disappearing_curvature _ hlevel
  refine ⟨max E.disappearing_start s, le_max_left _ _,
    max_lt E.disappearing_start_bounds.2 hsT, ?_⟩
  intro t ht x hx
  have htzero : 0 ≤ t.1 := E.tMinus_nonnegative.trans t.2.1
  have htmem : t.1 ∈ F.time_domain := I.time_domain_eq.symm.subset ⟨htzero, t.2.2⟩
  have hr : F.parameters.r T ≤ F.parameters.r t.1 :=
    F.parameters.r_antitone htzero I.terminal_pos.le t.2.2.le
  have hlevelt : (F.parameters.r t.1)⁻¹ ^ 2 ≤ (F.parameters.r T)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (F.parameters.r_pos t.1 htzero).le)
      ((inv_le_inv₀ (F.parameters.r_pos t.1 htzero) hrT).mpr hr) 2
  have hscalar := htail t.1 ⟨(le_max_right _ _).trans ht, t.2.2⟩ x hx
  have hpre : (E.pre_flow.connection t.1).scalarCurvature x =
      (Splice.connection F T C R t.1).scalarCurvature (E.pre_identify t x) :=
    (E.pre_flow.connection t.1).scalarCurvature_eq_of_local_isometry
      (Splice.connection F T C R t.1) isOpen_univ (E.pre_identify t).contMDiff.contMDiffOn
      (fun y _ v w => (E.pre_metric t y v w).symm) (mem_univ x)
  let e := Splice.identifyBefore F T C R t.1 t.2.2
  have hold := (F.connection t.1).scalarCurvature_eq_of_local_isometry
    (Splice.connection F T C R t.1) isOpen_univ e.contMDiff.contMDiffOn
    (fun y _ v w => (Splice.identifyBefore_metric F T C R t.1 t.2.2 y v w).symm)
    (mem_univ (e.symm (E.pre_identify t x)))
  have hident : (E.pre_flow.connection t.1).scalarCurvature x =
      (F.connection t.1).scalarCurvature (e.symm (E.pre_identify t x)) := by
    simp only [e.apply_symm_apply] at hold
    exact hpre.trans hold.symm
  rw [hident] at hscalar
  exact I.canonical t.1 htmem _ (hlevelt.trans hscalar.le)

def canonicalNonemptyEvent : SurgeryEventData F.standard_initial F.local_constants F.parameters
    (Splice.slice F T C R) (Splice.metric F T C R) T :=
  { E with
    disappearing_start := Classical.choose (exists_event_canonical_tail I C R E)
    disappearing_start_bounds :=
      ⟨E.disappearing_start_bounds.1.trans_le
        (Classical.choose_spec (exists_event_canonical_tail I C R E)).1,
        (Classical.choose_spec (exists_event_canonical_tail I C R E)).2.1⟩
    disappearing_cover := fun t ht => E.disappearing_cover t
      ⟨(Classical.choose_spec (exists_event_canonical_tail I C R E)).1.trans ht.1, ht.2⟩ }

theorem canonicalNonemptyEvent_start_le :
    E.disappearing_start ≤ (canonicalNonemptyEvent I C R E).disappearing_start :=
  (Classical.choose_spec (exists_event_canonical_tail I C R E)).1

theorem canonicalNonemptyEvent_control (t : Ico E.tMinus T)
    (ht : (canonicalNonemptyEvent I C R E).disappearing_start ≤ t.1)
    (x : (Splice.slice F T C R E.tMinus).carrier) (hx : x ∉ interior E.retained_pre) :
    SurgeryCanonicalControl F t.1
      ((Splice.identifyBefore F T C R t.1 t.2.2).symm (E.pre_identify t x))
      F.parameters.epsilon F.parameters.C :=
  (Classical.choose_spec (exists_event_canonical_tail I C R E)).2.2 t ht x hx

theorem canonicalNonemptyEvent_preservation :
    M33NonemptyEventDataPreservation E (canonicalNonemptyEvent I C R E) :=
  ⟨rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

def canonicalNonemptyEvent_terminalPolicy (h : SurgeryEventTerminalPolicy E) :
    SurgeryEventTerminalPolicy (canonicalNonemptyEvent I C R E) :=
  ⟨h.cuts, h.retained_eq⟩

end PoincareConjecture.Surgery.TerminalRestart
