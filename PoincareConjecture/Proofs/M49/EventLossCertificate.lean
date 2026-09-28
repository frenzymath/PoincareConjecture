import PoincareConjecture.Proofs.M49.DirectLeftLimitVolume
import PoincareConjecture.Proofs.M49.RetainedVolume












set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.M49




theorem exists_event_loss_certificate
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (c : ℝ) (hc : 0 < c)
    (hpinched : ∀ t ∈ Ico (F.event T hT).tMinus T,
      SurgeryPinchedAt (F.connection t) t)
    (hzero : (F.event T hT).cap_count = 0 →
      ∃ x : (F.slice (F.event T hT).tMinus).carrier,
        connectedComponent x ⊆ (F.event T hT).retained_preᶜ ∧
        0 < calibratedMetricVolume
          ((F.event T hT).pre_flow.metric (F.event T hT).tMinus)
          (connectedComponent x))
    (hper : ∀ i : Fin (F.event T hT).cap_count,
      calibratedMetricVolume (F.metric T) ((F.event T hT).caps i).carrier +
          ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) ≤
        calibratedMetricVolume (F.event T hT).limit_metric
          (((F.event T hT).necks i).neck.region 0
            ((F.event T hT).necks i).neck.epsilon⁻¹))
    (htotal : calibratedMetricVolume (F.metric T) univ +
        ((F.event T hT).cap_count : ℝ≥0∞) *
          ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) ≤
      calibratedMetricVolume (F.event T hT).limit_metric univ) :
    ∃ D : RepairedSurgeryEventLossData F T hT,
      D.loss = if (F.event T hT).cap_count = 0 then 0 else
        ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) := by
  let E := F.event T hT
  let q := ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T))
  let loss : ℝ≥0∞ := if E.cap_count = 0 then 0 else q
  have hT0 : 0 ≤ T := E.tMinus_nonnegative.trans E.tMinus_lt.le
  have hq : 0 < q := ENNReal.ofReal_pos.mpr
    (mul_pos hc (div_pos (pow_pos (F.parameters.h_pos T hT0) 3)
      (F.parameters.delta_pos T hT0)))
  have hselected : loss ≤ (E.cap_count : ℝ≥0∞) * q := by
    by_cases hn : E.cap_count = 0
    · change (if E.cap_count = 0 then 0 else q) ≤ _
      rw [if_pos hn]
      exact bot_le
    · have hn' : (1 : ℝ≥0∞) ≤ E.cap_count := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      simpa only [loss, if_neg hn, one_mul] using mul_le_mul' hn' (le_refl q)
  obtain ⟨L, hL, hlim⟩ := preEvent_exists_finite_left_limit_direct F T hT hpinched
  refine ⟨{
    loss := loss
    left_limit_volume := L
    left_limit_volume_ne_top := hL
    left_limit_volume_tendsto := hlim
    regular_limit_volume_le_left_limit :=
      event_regular_limit_volume_le_left_limit_direct F T hT hlim
    retained_volume_transport := event_retained_volume_eq E
    terminal_volume_drop := (add_le_add le_rfl hselected).trans htotal
    event_case := ?_ }, rfl⟩
  by_cases hn : E.cap_count = 0
  · exact Or.inr ⟨hn, by simp only [loss, if_pos hn], hzero hn⟩
  · let i : Fin E.cap_count := ⟨0, Nat.pos_of_ne_zero hn⟩
    refine Or.inl ⟨i, ?_, ?_⟩
    · simpa only [loss, if_neg hn] using hq
    · simpa only [loss, if_neg hn] using hper i

end PoincareConjecture.M49
