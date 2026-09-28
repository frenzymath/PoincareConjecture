import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Events.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Events.Identification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Gluing.AbsoluteFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Theory

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

private theorem metric_eq_of_inner {S : GeneralizedSliceCarrier.{u}}
    {g h : RiemannianMetric 3 S.carrier}
    (he : ∀ x v w, g.inner x v w = h.inner x v w) : g = h := by
  have hi : g.inner = h.inner := by
    funext x
    ext v w
    exact he x v w
  cases g
  cases h
  congr

theorem SurgeryRegularSlab.initial_metric
    {S : ℝ → GeneralizedSliceCarrier.{u}}
    {g : ∀ t, RiemannianMetric 3 (S t).carrier} {a b : ℝ}
    (A : SurgeryRegularSlab S g a b) : A.flow.metric a = g a := by
  apply metric_eq_of_inner
  intro x v w
  have hid : (⇑(A.identify ⟨a, le_rfl, A.ordered.le⟩)) = id :=
    funext A.initial_identify
  have hpair := congrArg (fun f : (S a).carrier → (S a).carrier =>
    (g a).inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x w)) hid
  simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] at hpair
  have he := A.metric_pullback ⟨a, le_rfl, A.ordered.le⟩ x v w
  exact he.symm.trans hpair

namespace Surgery.RegularHistory.EventTimeWindow

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F} {T : ℝ}
    {hT : T ∈ F.surgery_times} {hTW : T ∈ W.interval}
    [Nonempty (F.slice T).carrier] (A : EventTimeWindow W hT hTW)

theorem exists_flow_of_right_mem (hr : A.right ∈ W.interval) :
    ∃ H : RicciFlow 3 (EventIdentify.carrier hT).carrier A.interval,
      EqOn (F.event T hT).continuingPreFlow.metric H.metric (A.interval ∩ Iio T) ∧
      EqOn ((F.event T hT).continuingPostFlow (A.postSlab hr).flow).metric H.metric
        (A.interval ∩ Ici T) := by
  let B := A.postSlab hr
  let G : RicciFlow 3 (F.slice T).carrier (Ico T A.right) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow B.flow Ico_subset_Icc_self
      ordConnected_Ico
      ⟨T, ⟨le_rfl, A.right_gt⟩, (T + A.right) / 2,
        ⟨by linarith [A.right_gt], by linarith [A.right_gt]⟩,
        by linarith [A.right_gt]⟩
  have hG : G.metric T = F.metric T := B.initial_metric
  obtain ⟨H, hpre, hpost⟩ := (F.event T hT).exists_continuing_flow A.right_gt G hG
  have hsub : A.interval ⊆ Ico (F.event T hT).tMinus A.right := by
    intro t ht
    exact ⟨(A.pre_start_lt.trans ht.2.1).le, ht.2.2⟩
  refine ⟨Poincare.Geometry.RicciFlow.Harnack.restrictFlow H hsub
    A.interval_connected A.interval_nontrivial, ?_, ?_⟩
  · intro t ht
    exact hpre (A.pre_subset ht)
  · intro t ht
    exact hpost ⟨ht.2, ht.1.2.2⟩

theorem exists_flow_of_terminal
    (L : RicciFlowLocalTheory 3 (F.slice T).carrier)
    (hterminal : ∀ t ∈ W.interval, t ≤ T) :
    ∃ H : RicciFlow 3 (EventIdentify.carrier hT).carrier A.interval,
      EqOn (F.event T hT).continuingPreFlow.metric H.metric (A.interval ∩ Iio T) ∧
      ∀ (x : (EventIdentify.carrier hT).carrier) (v w : TangentSpace (𝓡 3) x),
        (H.metric T).inner x v w =
          (F.metric T).inner ((F.event T hT).retention.interiorMap x)
            (mfderiv (𝓡 3) (𝓡 3) (F.event T hT).retention.interiorMap x v)
            (mfderiv (𝓡 3) (𝓡 3) (F.event T hT).retention.interiorMap x w) := by
  obtain ⟨d, hd, G₀, hG₀⟩ := L.1 (F.metric T)
  let G : RicciFlow 3 (F.slice T).carrier (Ico T (T + d)) :=
    G₀.translate (-T)
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ordConnected_Ico
      ⟨T, ⟨le_rfl, by linarith⟩, T + d / 2,
        ⟨by linarith, by linarith⟩, by linarith⟩
  have hG : G.metric T = F.metric T := by
    change G₀.metric (T + -T) = F.metric T
    simpa only [add_neg_cancel] using hG₀
  obtain ⟨H, hpre, hpost⟩ := (F.event T hT).exists_continuing_flow (by linarith : T < T + d) G hG
  have hsub : A.interval ⊆ Ico (F.event T hT).tMinus (T + d) := by
    intro t ht
    exact ⟨(A.pre_start_lt.trans ht.2.1).le, lt_of_le_of_lt (hterminal t ht.1) (by linarith)⟩
  refine ⟨Poincare.Geometry.RicciFlow.Harnack.restrictFlow H hsub
    A.interval_connected A.interval_nontrivial, ?_, ?_⟩
  · intro t ht
    exact hpre (A.pre_subset ht)
  · intro x v w
    change (H.metric T).inner x v w = _
    rw [← hpost (show T ∈ Ico T (T + d) from ⟨le_rfl, by linarith⟩)]
    change (G.metric T).inner ((F.event T hT).retention.interiorMap x) _ _ = _
    rw [hG]
    rfl

end Surgery.RegularHistory.EventTimeWindow

end PoincareConjecture
