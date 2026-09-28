import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.OldEventPolicy









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SurgeryEventRebuild

theorem flow_inner_identify {s t : SliceMetric.{u}} (h : s = t) {J : Set ℝ}
    (X : RicciFlow 3 s.1.carrier J) (r : ℝ) (x : s.1.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    ((flow h X).metric r).inner (identify s t h x)
      (mfderiv (𝓡 3) (𝓡 3) (identify s t h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify s t h) x w) =
        (X.metric r).inner x v w := by
  subst t
  simp only [flow, identify, Diffeomorph.coe_refl, id_eq, mfderiv_id,
    ContinuousLinearMap.id_apply]

end PoincareConjecture.SurgeryEventRebuild

namespace PoincareConjecture.SurgeryVanishingEventData

open SurgeryEventRebuild

variable {P : SurgeryParameters} {past future : ℝ → SliceMetric.{u}} {T : ℝ}

noncomputable def copyBefore
    (E : SurgeryVanishingEventData P (fun t => (past t).1) (fun t => (past t).2) T)
    (hPast : ∀ t ∈ Ico 0 T, past t = future t) :
    SurgeryVanishingEventData P (fun t => (future t).1) (fun t => (future t).2) T := by
  have hm := hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩
  refine {
    tMinus := E.tMinus
    tMinus_nonnegative := E.tMinus_nonnegative
    tMinus_lt := E.tMinus_lt
    pre_nonempty := by rw [← hm]; exact E.pre_nonempty
    pre_flow := flow hm E.pre_flow
    pre_identify := fun t => diffeomorph hm
      (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2⟩) (E.pre_identify t)
    pre_initial := by
      intro x
      obtain ⟨y, rfl⟩ := (identify (past E.tMinus) (future E.tMinus) hm).surjective x
      exact (diffeomorph_apply hm hm
        (E.pre_identify ⟨E.tMinus, le_rfl, E.tMinus_lt⟩) y).trans
          (congrArg (identify (past E.tMinus) (future E.tMinus) hm) (E.pre_initial y))
    pre_metric := fun t => diffeomorph_flow_metric_pullback
      hm (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2⟩)
      E.pre_flow t.1 (E.pre_identify t) (E.pre_metric t)
    left_limit_volume := E.left_limit_volume
    left_limit_volume_tendsto := ?_
    disappearing_start := E.disappearing_start
    disappearing_start_bounds := E.disappearing_start_bounds
    disappearing_curvature := ?_
    disappearing_cover := ?_ }
  all_goals
    try dsimp only [flow, diffeomorph] at *
    generalize hval : future E.tMinus = m at *
    clear hval
    subst m
  · apply E.left_limit_volume_tendsto.congr'
    have hzero : 0 < T := E.tMinus_nonnegative.trans_lt E.tMinus_lt
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hzero)] with t ht ht0
    rw [hPast t ⟨ht0.le, ht⟩]
  · exact E.disappearing_curvature
  · exact E.disappearing_cover

variable (E : SurgeryVanishingEventData P (fun t => (past t).1) (fun t => (past t).2) T)
  (hPast : ∀ t ∈ Ico 0 T, past t = future t)

@[simp] theorem copyBefore_tMinus : (E.copyBefore hPast).tMinus = E.tMinus := rfl

@[simp] theorem copyBefore_disappearing_start :
    (E.copyBefore hPast).disappearing_start = E.disappearing_start := rfl

@[simp] theorem copyBefore_left_limit_volume :
    (E.copyBefore hPast).left_limit_volume = E.left_limit_volume := rfl

theorem copyBefore_pre_flow_heq : HEq (E.copyBefore hPast).pre_flow E.pre_flow :=
  flow_heq (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩) E.pre_flow

theorem copyBefore_pre_flow_inner (r : ℝ) (x : (past E.tMinus).1.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    let e := identify (past E.tMinus) (future E.tMinus)
      (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩)
    ((E.copyBefore hPast).pre_flow.metric r).inner (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
        (E.pre_flow.metric r).inner x v w :=
  flow_inner_identify (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩) E.pre_flow r x v w

theorem copyBefore_pre_identify_apply (t : Ico E.tMinus T)
    (x : (past E.tMinus).1.carrier) :
    (E.copyBefore hPast).pre_identify t
      (identify (past E.tMinus) (future E.tMinus)
        (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩) x) =
      identify (past t.1) (future t.1)
        (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2⟩) (E.pre_identify t x) :=
  diffeomorph_apply (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩)
    (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2⟩) (E.pre_identify t) x

theorem copyBefore_preservation : M33VanishingEventDataPreservation E (E.copyBefore hPast) where
  reference_eq := rfl
  pre_carrier_eq := congrArg Sigma.fst
    (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩).symm
  pre_flow_heq := E.copyBefore_pre_flow_heq hPast

theorem copyBefore_terminalPolicy (h : SurgeryVanishingEventTerminalPolicy E) :
    SurgeryVanishingEventTerminalPolicy (E.copyBefore hPast) :=
  (E.copyBefore_preservation hPast).transportPolicy rfl h

end PoincareConjecture.SurgeryVanishingEventData
