import PoincareConjecture.Proofs.M49.CapComparisonVolume
import PoincareConjecture.Proofs.M49.CompleteBallVolume
import PoincareConjecture.Proofs.M49.Mathlib.GramDensity

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M49

theorem metricSurgeryResult_cap_volume_le
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {S : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 S.carrier}
    {I : MetricSurgeryInput K g} (R : MetricSurgeryResult g₀ I)
    {eta : ℝ} (heta : 0 < eta) (heta₁ : eta < 1)
    (hgap : g₀.cylindrical_end.radius + 5 < eta⁻¹)
    (hmat : ∀ A : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) →
        (1 / 2 : ℝ) ≤ Real.sqrt A.det ∧ Real.sqrt A.det ≤ 2)
    (heps : I.neck.epsilon ≤ K.comparison_delta eta) :
    calibratedMetricVolume R.metric
        (closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) ≤
      ENNReal.ofReal (2 * I.neck.scale ^ 3) *
        calibratedMetricVolume g₀.metric (g₀.metric.ball 0 eta⁻¹) := by
  obtain ⟨C⟩ := R.standard_close eta heta heps
  have hcontain : closure (R.cap_map ''
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) ⊆
        C.map '' g₀.metric.ball 0 eta⁻¹ :=
    (closure_mono R.cap_outer_ball).trans
      ((closure_metric_ball_subset_ball R.metric R.tip
        (mul_pos I.neck.scale_pos (inv_pos.mpr heta))
        (mul_lt_mul_of_pos_left hgap I.neck.scale_pos)).trans C.image_contains)
  exact (measure_mono hcontain).trans
    (surgeryCapClose_volume_image_le C heta₁ hmat
      (isOpen_metric_ball g₀.metric 0 eta⁻¹).measurableSet subset_rfl)

set_option backward.isDefEq.respectTransparency false in

theorem exists_uniform_local_cap_volume_bound (g₀ : StandardInitialMetric) :
    ∃ Ccap : ℝ, 0 < Ccap ∧ ∀ K : MetricSurgeryConstants,
      ∃ d : ℝ, 0 < d ∧ d ≤ K.delta₀ ∧
        ∀ (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
          (I : MetricSurgeryInput K g) (R : MetricSurgeryResult g₀ I),
          I.neck.epsilon ≤ d →
            calibratedMetricVolume R.metric
                (closure (R.cap_map ''
                  g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) ≤
              ENNReal.ofReal (Ccap * I.neck.scale ^ 3) := by
  obtain ⟨e, he, hmatrix⟩ := Matrix.exists_pos_entrywise_sqrt_det_bounds (Fin 3)
  let eta : ℝ := min e (min (1 / 2) (g₀.cylindrical_end.radius + 6)⁻¹)
  have hrad : 0 < g₀.cylindrical_end.radius + 6 := by
    linarith [g₀.cylindrical_end.radius_pos]
  have heta : 0 < eta := lt_min he (lt_min (by norm_num) (inv_pos.mpr hrad))
  have heta₁ : eta < 1 :=
    ((min_le_right e _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hsmall : eta ≤ (g₀.cylindrical_end.radius + 6)⁻¹ :=
    (min_le_right e _).trans (min_le_right _ _)
  have hlarge : g₀.cylindrical_end.radius + 6 ≤ eta⁻¹ := by
    simpa only [inv_inv] using
      (inv_le_inv₀ (inv_pos.mpr hrad) heta).mpr hsmall
  have hgap : g₀.cylindrical_end.radius + 5 < eta⁻¹ := by linarith
  have hmat : ∀ A : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) →
        (1 / 2 : ℝ) ≤ Real.sqrt A.det ∧ Real.sqrt A.det ≤ 2 := by
    intro A hA
    have hc := hmatrix A (fun i j => by
      have heA := (hA i j).trans (min_le_left e _)
      by_cases hij : i = j
      · simpa only [if_pos hij] using heA
      · simpa only [if_neg hij] using heA)
    have hdec : (fun i j : Fin 3 => Classical.propDecidable (i = j)) =
        (inferInstance : DecidableEq (Fin 3)) := Subsingleton.elim _ _
    have hdet := congrArg (fun d : DecidableEq (Fin 3) =>
      @Matrix.det (Fin 3) d (Fin.fintype 3) ℝ Real.commRing A) hdec
    rw [hdet] at hc
    exact hc
  let V := calibratedMetricVolume g₀.metric (g₀.metric.ball 0 eta⁻¹)
  have hV : V ≠ ⊤ := (calibratedMetricVolume_ball_lt_top
    g₀.metric g₀.complete 0 eta⁻¹).ne
  refine ⟨2 * V.toReal + 1, by positivity, ?_⟩
  intro K
  refine ⟨min K.delta₀ (K.comparison_delta eta),
    lt_min K.delta₀_pos (K.comparison_delta_pos eta heta), min_le_left _ _, ?_⟩
  intro S g I R heps
  have hh := I.neck.scale_pos
  have hbound := metricSurgeryResult_cap_volume_le R heta heta₁ hgap hmat
    (heps.trans (min_le_right _ _))
  apply hbound.trans
  change ENNReal.ofReal (2 * I.neck.scale ^ 3) * V ≤ _
  calc
    _ = ENNReal.ofReal (2 * I.neck.scale ^ 3 * V.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * I.neck.scale ^ 3),
        ENNReal.ofReal_toReal hV]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [pow_nonneg hh.le 3])

end PoincareConjecture.M49
