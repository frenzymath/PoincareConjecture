import PoincareConjecture.Proofs.M51.EmptyEventCopy









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SurgeryVanishingEventData

variable {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}


noncomputable def reindexPast (E : SurgeryVanishingEventData P slice metric T)
    (tau : ℝ → ℝ) (hTau : ∀ t ≤ T, tau t = t) :
    SurgeryVanishingEventData P (fun t => slice (tau t))
      (fun t => metric (tau t)) T := by
  have hm := hTau E.tMinus E.tMinus_lt.le
  refine {
    tMinus := E.tMinus
    tMinus_nonnegative := E.tMinus_nonnegative
    tMinus_lt := E.tMinus_lt
    pre_nonempty := by rw [hm]; exact E.pre_nonempty
    pre_flow := M51EventCopy.flow slice hm.symm E.pre_flow
    pre_identify := fun t => M51EventCopy.diffeomorph slice hm.symm
      (hTau t.1 t.2.2.le).symm (E.pre_identify t)
    pre_initial := by
      intro x
      obtain ⟨y, rfl⟩ := (M51EventCopy.timeEquivalence slice E.tMinus
        (tau E.tMinus) hm.symm).surjective x
      exact (M51EventCopy.diffeomorph_apply slice hm.symm hm.symm
        (E.pre_identify ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩) y).trans
          (congrArg (M51EventCopy.timeEquivalence slice E.tMinus
            (tau E.tMinus) hm.symm) (E.pre_initial y))
    pre_metric := fun t => M51EventCopy.diffeomorph_flow_metric_pullback slice metric
      hm.symm (hTau t.1 t.2.2.le).symm E.pre_flow t.1
      (E.pre_identify t) (E.pre_metric t)
    left_limit_volume := E.left_limit_volume
    left_limit_volume_tendsto := ?_
    disappearing_start := E.disappearing_start
    disappearing_start_bounds := E.disappearing_start_bounds
    disappearing_curvature := ?_
    disappearing_cover := ?_ }
  all_goals
    try dsimp only [M51EventCopy.flow, M51EventCopy.diffeomorph] at *
    generalize hval : tau E.tMinus = m at *
    clear hval
    subst m
  · apply E.left_limit_volume_tendsto.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hTau t ht.le]
  · exact E.disappearing_curvature
  · exact E.disappearing_cover

variable (E : SurgeryVanishingEventData P slice metric T)
    (tau : ℝ → ℝ) (hTau : ∀ t ≤ T, tau t = t)

@[simp] theorem reindexPast_tMinus : (E.reindexPast tau hTau).tMinus = E.tMinus := rfl

@[simp] theorem reindexPast_disappearing_start :
    (E.reindexPast tau hTau).disappearing_start = E.disappearing_start := rfl

@[simp] theorem reindexPast_left_limit_volume :
    (E.reindexPast tau hTau).left_limit_volume = E.left_limit_volume := rfl

theorem reindexPast_pre_flow_heq : HEq (E.reindexPast tau hTau).pre_flow E.pre_flow :=
  M51EventCopy.flow_heq slice (hTau E.tMinus E.tMinus_lt.le).symm E.pre_flow

theorem reindexPast_pre_identify_apply (t : Set.Ico E.tMinus T)
    (x : (slice E.tMinus).carrier) :
    (E.reindexPast tau hTau).pre_identify t
      (M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le) x) =
        M51EventCopy.identify slice tau t.1 (hTau t.1 t.2.2.le) (E.pre_identify t x) :=
  M51EventCopy.diffeomorph_apply slice (hTau E.tMinus E.tMinus_lt.le).symm
    (hTau t.1 t.2.2.le).symm (E.pre_identify t) x

end PoincareConjecture.SurgeryVanishingEventData
