import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.UniformInitialCoordinates
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.EarlySlabComparison
import PoincareConjecture.Proofs.M34.Standard.CoordinateMetricBounds










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M34




theorem partialFlow_early_small_ball_volume {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : RicciFlowCurvatureTheory.{0})
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime) :
    ∃ r0 kappa : ℝ, 0 < r0 ∧ 0 < kappa ∧ ∀ t ∈ Icc 0 T,
      ∀ q : StandardCapSpace, ∀ r : ℝ, 0 < r → r ≤ r0 →
        ENNReal.ofReal (kappa * r ^ 3) ≤
          calibratedMetricVolume (F.flow.metric t) ((F.flow.metric t).ball q r) := by
  obtain ⟨delta, b, v0, hdelta, hb, hv0, hcharts⟩ :=
    uniform_initial_coordinate_volume g0.cylindrical_end
  obtain ⟨c, hc, hnorm⟩ := partialFlow_uniform_tangentNorm_comparison F P hT
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let d : ℝ := c * Real.sqrt b
  have hd : 0 < d := mul_pos hcpos (Real.sqrt_pos.mpr hb)
  let kappa : ℝ := v0 / (c ^ 3 * d ^ 3)
  have hkappa : 0 < kappa := div_pos hv0 (mul_pos (pow_pos hcpos _) (pow_pos hd _))
  refine ⟨delta * d, kappa, mul_pos hdelta hd, hkappa, ?_⟩
  intro t ht q r hr hr0
  let rho : ℝ := r / d
  have hrho : 0 < rho := div_pos hr hd
  have hrhodelta : rho ≤ delta := (div_le_iff₀ hd).mpr hr0
  obtain ⟨f, hf0, hsource, hcoeff, hvolume⟩ := hcharts q
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f (Metric.ball 0 (2 * delta)) :=
    (f.contMDiffOn_toFun.of_le (by simp)).mono hsource
  have hdiff : ∀ z ∈ Metric.ball 0 (2 * delta), ∀ w : StandardCapSpace,
      (F.flow.metric t).tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z w) ≤ d * ‖w‖ := by
    intro z hz w
    have h0 := tangentNorm_mfderiv_le_of_pullbackMetricForm_norm_le
      g0.metric f z hb.le (hcoeff z hz) w
    calc
      _ ≤ c * g0.metric.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z w) :=
        (hnorm t ht (f z) (mfderiv (𝓡 3) (𝓡 3) f z w)).2
      _ ≤ c * (Real.sqrt b * ‖w‖) := mul_le_mul_of_nonneg_left h0 hcpos.le
      _ = d * ‖w‖ := by dsimp [d]; ring
  have himage := coordinate_ball_subset_metric_ball (F.flow.metric t) f
    hdelta hd hrho hrhodelta hf hdiff
  have hdrho : d * rho = r := by dsimp [rho]; field_simp
  rw [hf0, hdrho] at himage
  let A : Set StandardCapSpace := f '' Metric.ball 0 rho
  have hmeasure : ENNReal.ofReal (v0 * rho ^ 3) ≤
      ENNReal.ofReal c ^ 3 * calibratedMetricVolume (F.flow.metric t) A :=
    (hvolume rho ⟨hrho, hrhodelta⟩).trans
      (calibratedMetricVolume_le_of_tangentNorm_le (F.flow.metric t) g0.metric hcpos
        (fun x w => (hnorm t ht x w).1) A)
  have hc3 : 0 < c ^ 3 := pow_pos hcpos _
  have hdiv : ENNReal.ofReal (v0 * rho ^ 3) / ENNReal.ofReal (c ^ 3) ≤
      calibratedMetricVolume (F.flow.metric t) A := by
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hc3).ne' ENNReal.ofReal_ne_top).mpr
    simpa only [ENNReal.ofReal_pow hcpos.le, mul_comm] using hmeasure
  calc
    ENNReal.ofReal (kappa * r ^ 3) = ENNReal.ofReal ((v0 * rho ^ 3) / c ^ 3) := by
      congr 1
      dsimp [kappa, rho]
      field_simp
    _ = ENNReal.ofReal (v0 * rho ^ 3) / ENNReal.ofReal (c ^ 3) :=
      ENNReal.ofReal_div_of_pos hc3
    _ ≤ calibratedMetricVolume (F.flow.metric t) A := hdiv
    _ ≤ _ := measure_mono himage

end PoincareConjecture.M34
