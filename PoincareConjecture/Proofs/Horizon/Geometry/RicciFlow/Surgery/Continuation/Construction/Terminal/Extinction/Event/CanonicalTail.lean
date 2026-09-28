import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.Extinction

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)

include I

theorem exists_event_canonical_tail : ∃ s : ℝ, V.disappearing_start ≤ s ∧ s < T ∧
    ∀ t : Ico V.tMinus T, s ≤ t.1 → ∀ x : (F.slice V.tMinus).carrier,
      SurgeryCanonicalControl F t.1 (V.pre_identify t x) F.parameters.epsilon F.parameters.C := by
  have hrT : 0 < F.parameters.r T := F.parameters.r_pos T I.terminal_pos.le
  have hinv : (F.parameters.r T)⁻¹ < I.rho⁻¹ :=
    (inv_lt_inv₀ hrT I.rho_pos).mpr I.rho_lt_r
  have hlevel : (F.parameters.r T)⁻¹ ^ 2 < (F.parameters.delta T * F.parameters.r T)⁻¹ ^ 2 := by
    rw [← I.rho_eq]
    have := inv_pos.mpr hrT
    nlinarith
  obtain ⟨s, _hs, hsT, htail⟩ := V.disappearing_curvature _ hlevel
  refine ⟨max V.disappearing_start s, le_max_left _ _,
    max_lt V.disappearing_start_bounds.2 hsT, ?_⟩
  intro t ht x
  have htzero : 0 ≤ t.1 := V.tMinus_nonnegative.trans t.2.1
  have htmem : t.1 ∈ F.time_domain := I.time_domain_eq ▸ (show t.1 ∈ Ico 0 T from ⟨htzero, t.2.2⟩)
  have hr : F.parameters.r T ≤ F.parameters.r t.1 :=
    F.parameters.r_antitone htzero I.terminal_pos.le t.2.2.le
  have hlevelt : (F.parameters.r t.1)⁻¹ ^ 2 ≤ (F.parameters.r T)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (F.parameters.r_pos t.1 htzero).le)
      ((inv_le_inv₀ (F.parameters.r_pos t.1 htzero) hrT).mpr hr) 2
  have hscalar := htail t.1 ⟨(le_max_right _ _).trans ht, t.2.2⟩ x
  have hident : (V.pre_flow.connection t.1).scalarCurvature x =
      (F.connection t.1).scalarCurvature (V.pre_identify t x) :=
    (V.pre_flow.connection t.1).scalarCurvature_eq_of_local_isometry
      (F.connection t.1) isOpen_univ (V.pre_identify t).contMDiff.contMDiffOn
      (fun y _ v w => (V.pre_metric t y v w).symm) (mem_univ x)
  rw [hident] at hscalar
  exact I.canonical t.1 htmem _ (hlevelt.trans hscalar.le)

def canonicalVanishingEvent : SurgeryVanishingEventData F.parameters F.slice F.metric T :=
  { V with
    disappearing_start := Classical.choose (exists_event_canonical_tail I V)
    disappearing_start_bounds :=
      ⟨V.disappearing_start_bounds.1.trans_le
        (Classical.choose_spec (exists_event_canonical_tail I V)).1,
        (Classical.choose_spec (exists_event_canonical_tail I V)).2.1⟩
    disappearing_cover := fun t ht => V.disappearing_cover t
      ⟨(Classical.choose_spec (exists_event_canonical_tail I V)).1.trans ht.1, ht.2⟩ }

theorem canonicalVanishingEvent_control (t : Ico V.tMinus T)
    (ht : (canonicalVanishingEvent I V).disappearing_start ≤ t.1)
    (x : (F.slice V.tMinus).carrier) :
    SurgeryCanonicalControl F t.1 (V.pre_identify t x) F.parameters.epsilon F.parameters.C :=
  (Classical.choose_spec (exists_event_canonical_tail I V)).2.2 t ht x

theorem canonicalVanishingEvent_preservation :
    M33VanishingEventDataPreservation V (canonicalVanishingEvent I V) :=
  ⟨rfl, rfl, HEq.rfl⟩

theorem canonicalVanishingEvent_terminalPolicy (h : SurgeryVanishingEventTerminalPolicy V) :
    SurgeryVanishingEventTerminalPolicy (canonicalVanishingEvent I V) := h

end PoincareConjecture.Surgery.Extinction
