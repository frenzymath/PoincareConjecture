import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.EventPreservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SurgeryVanishingEventData

open SurgeryEventRebuild

variable {P : SurgeryParameters} {past future : ℝ → SliceMetric.{u}} {T : ℝ}

noncomputable def copyPast
    (E : SurgeryVanishingEventData P (fun t => (past t).1) (fun t => (past t).2) T)
    (hPast : ∀ t ∈ Set.Icc 0 T, past t = future t) :
    SurgeryVanishingEventData P (fun t => (future t).1) (fun t => (future t).2) T := by
  have hm := hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
  refine {
    tMinus := E.tMinus
    tMinus_nonnegative := E.tMinus_nonnegative
    tMinus_lt := E.tMinus_lt
    pre_nonempty := by rw [← hm]; exact E.pre_nonempty
    pre_flow := flow hm E.pre_flow
    pre_identify := fun t => diffeomorph hm
      (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩) (E.pre_identify t)
    pre_initial := by
      intro x
      obtain ⟨y, rfl⟩ := (identify (past E.tMinus) (future E.tMinus) hm).surjective x
      exact (diffeomorph_apply hm hm
        (E.pre_identify ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩) y).trans
          (congrArg (identify (past E.tMinus) (future E.tMinus) hm) (E.pre_initial y))
    pre_metric := fun t => diffeomorph_flow_metric_pullback
      hm (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩)
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
    rw [hPast t ⟨ht0.le, ht.le⟩]
  · exact E.disappearing_curvature
  · exact E.disappearing_cover

variable (E : SurgeryVanishingEventData P (fun t => (past t).1) (fun t => (past t).2) T)
    (hPast : ∀ t ∈ Set.Icc 0 T, past t = future t)

@[simp] theorem copyPast_tMinus : (E.copyPast hPast).tMinus = E.tMinus := rfl

@[simp] theorem copyPast_disappearing_start :
    (E.copyPast hPast).disappearing_start = E.disappearing_start := rfl

@[simp] theorem copyPast_left_limit_volume :
    (E.copyPast hPast).left_limit_volume = E.left_limit_volume := rfl

theorem copyPast_pre_flow_heq : HEq (E.copyPast hPast).pre_flow E.pre_flow :=
  flow_heq (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) E.pre_flow

theorem copyPast_pre_identify_apply (t : Set.Ico E.tMinus T)
    (x : (past E.tMinus).1.carrier) :
    (E.copyPast hPast).pre_identify t
      (identify (past E.tMinus) (future E.tMinus)
        (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) x) =
      identify (past t.1) (future t.1)
        (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩) (E.pre_identify t x) :=
  diffeomorph_apply (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩)
    (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩) (E.pre_identify t) x

theorem copyPast_preservation : M33VanishingEventDataPreservation E (E.copyPast hPast) where
  reference_eq := rfl
  pre_carrier_eq := congrArg Sigma.fst (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩).symm
  pre_flow_heq := E.copyPast_pre_flow_heq hPast

end PoincareConjecture.SurgeryVanishingEventData
