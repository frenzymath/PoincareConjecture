import PoincareConjecture.Proofs.M49.RetainedVolume
import PoincareConjecture.Proofs.M49.EventCapVolume
import PoincareConjecture.Proofs.M49.Lemma17_12_NeckVolume










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal BigOperators

universe u

namespace PoincareConjecture.M49



theorem event_total_volume_add_cap_losses_le
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T) (loss : ℝ≥0∞)
    (hloss : ∀ i : Fin E.cap_count,
      calibratedMetricVolume (metric T) (E.caps i).carrier + loss ≤
        calibratedMetricVolume E.limit_metric
          ((E.necks i).neck.region 0 (E.necks i).neck.epsilon⁻¹)) :
    calibratedMetricVolume (metric T) univ + (E.cap_count : ℝ≥0∞) * loss ≤
      calibratedMetricVolume E.limit_metric univ := by
  classical
  let R := E.limit_identify.map '' E.retained_pre
  let A := fun i : Fin E.cap_count =>
    (E.necks i).neck.region 0 (E.necks i).neck.epsilon⁻¹
  have hA (i : Fin E.cap_count) : MeasurableSet (A i) := by
    let N := (E.necks i).neck
    have h0 : -N.epsilon⁻¹ ≤ (0 : ℝ) := neg_nonpos.mpr (inv_pos.mpr N.epsilon_pos).le
    rw [show A i = N.region 0 N.epsilon⁻¹ from rfl,
      ← epsilonNeckChart_image_region N 0 N.epsilon⁻¹ h0 le_rfl]
    apply IsOpen.measurableSet
    apply (epsilonNeckChart N).isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
    intro z hz
    exact ⟨mem_univ _, h0.trans_lt hz.2.1, hz.2.2⟩
  have hdis : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    exact (E.neck_carrier_disjoint i j hij).mono
      (fun _ hx => hx.1) (fun _ hx => hx.1)
  have hRdis : Disjoint R (⋃ i, A i) := by
    apply disjoint_iUnion_right.mpr
    intro i
    exact (E.neck_positive_discarded i).symm
  have hpost : calibratedMetricVolume (metric T) univ ≤
      calibratedMetricVolume (metric T) E.retained_post +
        ∑ i, calibratedMetricVolume (metric T) (E.caps i).carrier := by
    rw [← E.post_cover]
    exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
  have hterminal : calibratedMetricVolume E.limit_metric R +
      ∑ i, calibratedMetricVolume E.limit_metric (A i) ≤
        calibratedMetricVolume E.limit_metric univ := by
    have hvolA : calibratedMetricVolume E.limit_metric (⋃ i, A i) =
        ∑ i, calibratedMetricVolume E.limit_metric (A i) := by
      rw [measure_iUnion hdis hA, tsum_fintype]
    rw [← hvolA, ← measure_union hRdis (MeasurableSet.iUnion hA)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ (calibratedMetricVolume (metric T) E.retained_post +
        ∑ i, calibratedMetricVolume (metric T) (E.caps i).carrier) +
          (E.cap_count : ℝ≥0∞) * loss := add_le_add hpost le_rfl
    _ = calibratedMetricVolume E.limit_metric R +
        ∑ i, (calibratedMetricVolume (metric T) (E.caps i).carrier + loss) := by
      rw [event_retained_volume_eq E, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact add_assoc _ _ _
    _ ≤ calibratedMetricVolume E.limit_metric R +
        ∑ i, calibratedMetricVolume E.limit_metric (A i) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hloss i))
    _ ≤ _ := hterminal



theorem exists_uniform_event_volume_loss (g₀ : StandardInitialMetric) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : MetricSurgeryConstants,
      ∃ d : ℝ, 0 < d ∧ d ≤ K.delta₀ ∧
        ∀ (P : SurgeryParameters) (slice : ℝ → GeneralizedSliceCarrier.{u})
          (metric : ∀ t, RiemannianMetric 3 (slice t).carrier) (T : ℝ)
          (E : SurgeryEventData g₀ K P slice metric T),
          P.delta T ≤ d →
            (∀ i : Fin E.cap_count,
              calibratedMetricVolume (metric T) (E.caps i).carrier +
                  ENNReal.ofReal (c * ((P.h T) ^ 3 / P.delta T)) ≤
                calibratedMetricVolume E.limit_metric
                  ((E.necks i).neck.region 0 (E.necks i).neck.epsilon⁻¹)) ∧
            calibratedMetricVolume (metric T) univ + (E.cap_count : ℝ≥0∞) *
                ENNReal.ofReal (c * ((P.h T) ^ 3 / P.delta T)) ≤
              calibratedMetricVolume E.limit_metric univ := by
  obtain ⟨cn, dn, hcn, hdn, hneck⟩ := exists_uniform_positive_half_neck_volume.{u}
  obtain ⟨Ccap, hCcap, hcap⟩ := exists_uniform_event_cap_volume_bound.{u} g₀
  refine ⟨cn / 2, half_pos hcn, ?_⟩
  intro K
  obtain ⟨dc, hdc, hdcK, hcapK⟩ := hcap K
  let d := min dc (min dn (cn / (2 * Ccap)))
  have hd : 0 < d := lt_min hdc (lt_min hdn (div_pos hcn (mul_pos (by norm_num) hCcap)))
  refine ⟨d, hd, (min_le_left _ _).trans hdcK, ?_⟩
  intro P slice metric T E hdelta
  have hT : 0 ≤ T := E.tMinus_nonnegative.trans E.tMinus_lt.le
  have hp : 0 < P.h T := P.h_pos T hT
  have hdp : 0 < P.delta T := P.delta_pos T hT
  have hc := hcapK P slice metric T E (hdelta.trans (min_le_left _ _))
  have hsmall : P.delta T ≤ cn / (2 * Ccap) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have habsorb : Ccap * (P.h T) ^ 3 ≤ cn / 2 * ((P.h T) ^ 3 / P.delta T) := by
    have hm : P.delta T * (2 * Ccap) ≤ cn :=
      (le_div_iff₀ (mul_pos (by norm_num) hCcap)).mp hsmall
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hdp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hm (pow_nonneg hp.le 3)]
  have hper (i : Fin E.cap_count) :
      calibratedMetricVolume (metric T) (E.caps i).carrier +
          ENNReal.ofReal (cn / 2 * ((P.h T) ^ 3 / P.delta T)) ≤
        calibratedMetricVolume E.limit_metric
          ((E.necks i).neck.region 0 (E.necks i).neck.epsilon⁻¹) := by
    have hn := hneck E.terminal.carrier E.limit_metric (E.necks i).neck (by
      rw [E.neck_delta i]
      exact hdelta.trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [E.neck_scale i, E.neck_delta i] at hn
    calc
      _ ≤ ENNReal.ofReal (Ccap * (P.h T) ^ 3) +
          ENNReal.ofReal (cn / 2 * ((P.h T) ^ 3 / P.delta T)) := add_le_add (hc i) le_rfl
      _ ≤ ENNReal.ofReal (cn / 2 * ((P.h T) ^ 3 / P.delta T)) +
          ENNReal.ofReal (cn / 2 * ((P.h T) ^ 3 / P.delta T)) :=
        add_le_add (ENNReal.ofReal_le_ofReal habsorb) le_rfl
      _ = ENNReal.ofReal (cn * (P.h T) ^ 3 / P.delta T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := by simpa only [E.neck_delta i] using hn
  exact ⟨hper, event_total_volume_add_cap_losses_le E _ hper⟩

end PoincareConjecture.M49
