import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M51.EventLimitEquivalence
import PoincareConjecture.Proofs.M51.CompactMetricLimit
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryFlowData

theorem lastRegularStart (F : SurgeryFlowData.{u}) {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
    ∃ a : ℝ, a ∈ F.time_domain ∧ (a = 0 ∨ a ∈ F.surgery_times) ∧ a < T ∧
      Ico a T ⊆ F.time_domain ∧ Disjoint F.surgery_times (Ioo a T) ∧
      Nonempty (F.slice a).carrier := by
  classical
  have hTpos : 0 < T := (F.event T hT).tMinus_nonnegative.trans_lt
    (F.event T hT).tMinus_lt
  let W := F.closedRegularHistoryWindow T hTpos (F.surgery_times_subset hT) inferInstance
  have hfinite : (F.surgery_times ∩ Ico 0 T).Finite :=
    W.events_finite.subset (inter_subset_inter_right _ Ico_subset_Icc_self)
  let s := insert 0 hfinite.toFinset
  have h0s : (0 : ℝ) ∈ s := Finset.mem_insert_self _ _
  let a := s.max' ⟨0, h0s⟩
  have ha : a ∈ s := Finset.max'_mem _ _
  have ha0 : 0 ≤ a := Finset.le_max' _ _ h0s
  have hchoice : a = 0 ∨ a ∈ F.surgery_times ∩ Ico 0 T := by
    simpa only [s, Finset.mem_insert, Set.Finite.mem_toFinset] using ha
  have halt : a < T := hchoice.elim (fun h => h ▸ hTpos) (fun h => h.2.2)
  have hamem : a ∈ F.time_domain :=
    hchoice.elim (fun h => h ▸ F.zero_mem) (fun h => F.surgery_times_subset h.1)
  refine ⟨a, hamem, hchoice.imp_right (fun h => h.1), halt,
    (fun t ht => F.time_domain_interval.out hamem (F.surgery_times_subset hT)
      ⟨ht.1, ht.2.le⟩),
    ?_, W.slice_nonempty a ⟨ha0, halt.le⟩⟩
  apply Set.disjoint_left.mpr
  intro t hts ht
  have hmem : t ∈ s := Finset.mem_insert_of_mem
    (hfinite.mem_toFinset.mpr ⟨hts, ha0.trans ht.1.le, ht.2⟩)
  exact (Finset.le_max' _ _ hmem).not_gt ht.1

theorem event_regularLimit_ne_univ (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3) {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
    (F.event T hT).regular_limit ≠ univ := by
  intro hfull
  let E := F.event T hT
  let f := E.limitDiffeomorph hfull
  have hpretime : E.tMinus ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
      ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
  have hlim : SurgeryMetricLimitOn (F.slice E.tMinus) E.terminal E.pre_flow.metric
      E.limit_metric f univ T := by
    change SurgeryMetricLimitOn (F.slice E.tMinus) E.terminal E.pre_flow.metric
      E.limit_metric E.limit_identify.map univ T
    rw [← hfull]
    exact E.metric_converges
  obtain ⟨d, hd, L, _, hbound⟩ := SurgeryMetricLimitOn.curvature_bound_of_compact
    (F.slice E.tMinus) E.terminal E.pre_flow.metric E.pre_flow.connection
    E.limit_metric f T (F.slices_compact E.tMinus hpretime) hlim
  obtain ⟨a, ha, hstart, haT, hI, hfree, hne⟩ := F.lastRegularStart hT
  let : Nonempty (F.slice a).carrier := hne
  let s := max E.tMinus (T - d / 2)
  have hs : s < T := max_lt E.tMinus_lt (by linarith)
  obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals a T ha hstart haT hI hfree
    (Or.inl hT) L s hs
  have hst : s < t := (le_max_right a s).trans_lt ht.1
  have htpre : t ∈ Ico E.tMinus T :=
    ⟨((le_max_left E.tMinus (T - d / 2)).trans hst.le), ht.2⟩
  have hcollar : t ∈ Ioo (T - d) T := by
    refine ⟨?_, ht.2⟩
    have := (le_max_right E.tMinus (T - d / 2)).trans_lt hst
    linarith
  let e := E.pre_identify ⟨t, htpre⟩
  have hmetric : MetricHomothety (E.pre_flow.metric t) (F.metric t) e 1 := by
    intro y v w
    simpa only [one_mul] using E.pre_metric ⟨t, htpre⟩ y v w
  have H := H13.metric_homothety _ _ (E.pre_flow.metric t) (F.metric t) e 1
    (by norm_num) hmetric
  have hnorm := H.curvature_norm_eq (E.pre_flow.connection t) (F.connection t) (e.symm x)
  rw [e.apply_symm_apply, div_one] at hnorm
  exact hx.not_ge (hnorm.trans_le (hbound t hcollar (e.symm x)))

theorem event_retainedPre_ne_univ (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3) {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
    (F.event T hT).retained_pre ≠ univ := by
  intro hfull
  apply F.event_regularLimit_ne_univ H13 hT
  apply Set.eq_univ_of_univ_subset
  rw [← hfull]
  exact (F.event T hT).retained_pre_subset

end PoincareConjecture.SurgeryFlowData
