import PoincareConjecture.Proofs.M15.Prop8_2_UpperBound
import PoincareConjecture.Proofs.M15.Thm8_1_Reduction
import PoincareConjecture.Proofs.M15.Thm8_1_DimensionZero

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem generalizedUniformTheorem
    (hM04 : RicciFlowCurvatureTheory.{u}) (n : ℕ)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (hM14 : GeneralizedLGeometryTheory.{u} n) :
    M15GeneralizedUniformTheorem.{u} n := by
  by_cases hn : n = 0
  · subst n
    exact generalizedUniformTheorem_zero
  have hnpos : 0 < (n : ℝ) / 2 :=
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (by norm_num)
  obtain ⟨epsilon0, hepsilon0, hepsilon0half, hupper⟩ :=
    exists_actualBallCylinder_reducedVolume_bound hM04 n hM12 hM13
  intro taubar l₀ V htaubar hl₀ hV
  have hlower : 0 < reducedVolumeLowerBound n taubar l₀ V :=
    reducedVolumeLowerBound_pos htaubar hV
  have hf : ContinuousAt (fun e : ℝ => 3 * Real.rpow e ((n : ℝ) / 2)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 _ (Or.inr hnpos.le))
  have hf0 : 3 * Real.rpow (0 : ℝ) ((n : ℝ) / 2) <
      reducedVolumeLowerBound n taubar l₀ V := by
    simpa only [Real.rpow_eq_pow, Real.zero_rpow (ne_of_gt hnpos), mul_zero] using hlower
  have hN : ∀ᶠ e : ℝ in 𝓝 0,
      3 * Real.rpow e ((n : ℝ) / 2) < reducedVolumeLowerBound n taubar l₀ V :=
    hf (Iio_mem_nhds hf0)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hN
  let epsilon := min epsilon0 (delta / 2)
  have hepsilon : 0 < epsilon := lt_min hepsilon0 (half_pos hdelta)
  have hepsilon_le : epsilon ≤ epsilon0 := min_le_left _ _
  have hedelta : epsilon < delta := (min_le_right _ _).trans_lt (half_lt_self hdelta)
  have hsmall : 3 * Real.rpow epsilon ((n : ℝ) / 2) <
      reducedVolumeLowerBound n taubar l₀ V := hball (by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hepsilon]
          using hedelta)
  refine ⟨{
    taubar_pos := htaubar
    l₀_pos := hl₀
    V_pos := hV
    kappa := epsilon ^ n
    kappa_pos := pow_pos hepsilon n
    estimate := ?_
  }⟩
  intro X _ time I G T x E r K C _ _ _ _ _ B D
  have htau : 0 < epsilon * r ^ 2 := mul_pos hepsilon (sq_pos_of_pos B.radius_pos)
  have htime : epsilon * r ^ 2 ≤ D.tau₀ := by
    apply le_trans _ D.radius_sq_le_tau₀
    have he : epsilon ≤ 1 := (hepsilon_le.trans hepsilon0half).trans (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (sq_nonneg r)
  obtain ⟨H, hWH, A, hlowerA⟩ := configuration_reducedVolume_lower_bound hM14 D hl₀.le hV
    (epsilon * r ^ 2) htau htime
  obtain ⟨L⟩ := hM14.conclusion X time I G
  obtain ⟨S⟩ := L.reduced_volume_source
  by_contra h
  have hvolume : calibratedMetricVolume (G.slices T).metricOnPoints
      ((G.slices T).metricOnPoints.ball x r) ≤ ENNReal.ofReal (epsilon ^ n * r ^ n) :=
    (lt_of_not_ge h).le
  have hbound := hupper X time I G T x r K C B D.terminal_ball_compact
    E epsilon hepsilon hepsilon_le H S A D.W D.W_open.measurableSet hWH hvolume
  exact (not_le_of_gt hsmall) (hlowerA.trans hbound)

end PoincareConjecture.Proofs.M15
