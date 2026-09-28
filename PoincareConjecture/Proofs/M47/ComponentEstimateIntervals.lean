import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalIntervals
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CompactCurvatureBound
import PoincareConjecture.Proofs.M13.ContractionTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

set_option maxHeartbeats 1200000 in

theorem component_event_preterminal_surgery_free
    (F : SurgeryFlowData.{u}) {T : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] :
    Disjoint F.surgery_times (Ioo (F.event T hT).tMinus T) := by
  let event := F.event T hT
  have hdomain := F.surgery_times_subset hT
  have hprefix : Icc 0 T ⊆ F.time_domain :=
    F.time_domain_interval.out F.zero_mem hdomain
  have hminus : event.tMinus ∈ F.time_domain :=
    hprefix ⟨event.tMinus_nonnegative, event.tMinus_lt.le⟩
  apply Set.disjoint_left.mpr
  intro S hS hSI
  let := M44.slice_nonempty_of_later F (F.surgery_times_subset hS) hdomain hSI.2.le
  let c := (event.tMinus + S) / 2
  have hc : event.tMinus < c ∧ c < S := by
    dsimp only [c]
    constructor <;> linarith [hSI.1]
  have hrect : Icc c S ×ˢ (univ : Set (F.slice event.tMinus).carrier) ⊆
      Ico event.tMinus T ×ˢ univ :=
    fun _ hp => ⟨⟨hc.1.le.trans hp.1.1, hp.1.2.trans_lt hSI.2⟩, hp.2⟩
  have hcompact : IsCompact (Icc c S ×ˢ (univ : Set (F.slice event.tMinus).carrier)) :=
    isCompact_Icc.prod (F.slices_compact event.tMinus hminus)
  have hnorm : ContinuousOn
      (fun p : ℝ × (F.slice event.tMinus).carrier =>
        (event.pre_flow.connection p.1).curvatureTensorNorm p.2) (Icc c S ×ˢ univ) :=
    (M34.continuousOn_flow_curvatureTensorNorm event.pre_flow).mono hrect
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hnorm
  have hbound (t : ℝ) (ht : t ∈ Icc c S) (x : (F.slice t).carrier) :
      (F.connection t).curvatureTensorNorm x ≤ B := by
    have htime : t ∈ Ico event.tMinus T :=
      ⟨hc.1.le.trans ht.1, ht.2.trans_lt hSI.2⟩
    let q := (event.pre_identify ⟨t, htime⟩).symm x
    have hhom : MetricHomothety (event.pre_flow.metric t) (F.metric t)
        (event.pre_identify ⟨t, htime⟩) 1 := by
      intro y v w
      simpa only [one_mul] using event.pre_metric ⟨t, htime⟩ y v w
    have heq := M13.homothety_curvatureTensorNorm_eq _ _ _ 1 zero_lt_one hhom
      (event.pre_flow.connection t) (F.connection t) q
    have heqx : (F.connection t).curvatureTensorNorm x =
        (event.pre_flow.connection t).curvatureTensorNorm q := by
      simpa only [q, Diffeomorph.apply_symm_apply, div_one] using heq
    have hBq : (event.pre_flow.connection t).curvatureTensorNorm q ≤ B := by
      apply hB
      exact ⟨(t, q), ⟨ht, mem_univ q⟩, rfl⟩
    exact heqx.trans_le hBq
  obtain ⟨t, ht, x, hx⟩ := M44.curvature_unbounded_before_surgery F hS B c hc.2
  exact (not_lt_of_ge (hbound t ⟨ht.1.le, ht.2.le⟩ x)) hx

end PoincareConjecture.M47
