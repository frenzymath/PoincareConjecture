import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.FrechetKolmogorov
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.Translation

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Convolution

namespace Poincare.Analysis.Spectral.Counting

open Poincare.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_mollifierEps_convolution_sub_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    eLpNorm (fun x =>
      (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x)
      p volume ≤
      ENNReal.ofReal ε * eLpNorm (fun x => ‖fderiv ℝ u x‖) p volume := by
  apply eLpNorm_convolution_sub_le_of_ae_translation_bound hp_one hp_top
    (mollifierEps_continuous hε) (mollifierEps_compactSupport hε)
    (mollifierEps_nonneg hε) (mollifierEps_integral_eq_one hε)
    hu.continuous.measurable hu.continuous.locallyIntegrable
  filter_upwards with s hs
  have hsε : ‖s‖ ≤ ε := by
    have hs_mem : s ∈ Function.support (mollifierEps (d := d) hε) := hs
    simpa using mollifierEps_support_subset_closedBall_eps hε hs_mem
  calc
    eLpNorm (fun x => u (x - s) - u x) p volume
        = eLpNorm (fun x => u x - u (x - s)) p volume := by
          apply eLpNorm_congr_norm_ae
          filter_upwards with x
          exact norm_sub_rev _ _
    _ ≤ ENNReal.ofReal ‖s‖ * eLpNorm (fun x => ‖fderiv ℝ u x‖) p volume :=
      eLpNorm_translate_sub_le_smul_eLpNorm_fderiv hp_one hp_top hu s
    _ ≤ ENNReal.ofReal ε * eLpNorm (fun x => ‖fderiv ℝ u x‖) p volume := by
      gcongr

theorem integral_mollifierEps_convolution_sub_sq_le
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_compact : HasCompactSupport u) :
    (∫ x : E,
      ((mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) ^ 2) ≤
      ε ^ 2 * ∫ x : E, ‖fderiv ℝ u x‖ ^ 2 := by
  have hd : MemLp (fun x : E => ‖fderiv ℝ u x‖) 2 volume :=
    (hu.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport
      (hu_compact.fderiv ℝ).norm
  have he : MemLp (fun x : E =>
      (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x)
      2 volume := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact ((mollifierEps_compactSupport hε).continuous_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (mollifierEps_continuous hε)
        hu.continuous.locallyIntegrable).sub hu.continuous
    · exact ((mollifierEps_compactSupport hε).convolution
        (ContinuousLinearMap.lsmul ℝ ℝ) hu_compact).sub hu_compact
  have h := eLpNorm_mollifierEps_convolution_sub_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hε hu
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    hd.eLpNorm_lt_top.ne) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le] at hr
  have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg hr 2
  rwa [mul_pow, eLpNorm_toReal_sq_eq_integral he,
    eLpNorm_toReal_sq_eq_integral hd] at hs

theorem mollifierEps_le_inv_volume_innerBall {ε : ℝ} (hε : 0 < ε) (x : E) :
    mollifierEps hε x ≤
      1 / (volume : Measure E).real (closedBall (0 : E) (ε / 2)) := by
  exact (mollifierBumpEps (d := d) hε).normed_le_div_measure_closedBall_rIn volume x

theorem integral_mollifierEps_sq_le_inv_volume_innerBall
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x : E, (mollifierEps hε x) ^ 2) ≤
      1 / (volume : Measure E).real (closedBall (0 : E) (ε / 2)) := by
  have h_compact : HasCompactSupport (fun x : E => (mollifierEps hε x) ^ 2) := by
    apply (mollifierEps_compactSupport (d := d) hε).mono
    intro x hx
    change mollifierEps hε x ≠ 0
    intro hx0
    exact hx (by simp [hx0])
  have h_int : Integrable (fun x : E => (mollifierEps hε x) ^ 2) volume :=
    ((mollifierEps_continuous hε).pow 2).integrable_of_hasCompactSupport h_compact
  calc
    (∫ x : E, (mollifierEps hε x) ^ 2) ≤
        ∫ x : E, mollifierEps hε x *
          (1 / (volume : Measure E).real (closedBall (0 : E) (ε / 2))) := by
      apply integral_mono h_int ((mollifierEps_integrable hε).mul_const _)
      intro x
      dsimp only
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (mollifierEps_le_inv_volume_innerBall hε x)
        (mollifierEps_nonneg hε x)
    _ = 1 / (volume : Measure E).real (closedBall (0 : E) (ε / 2)) := by
      rw [integral_mul_const, mollifierEps_integral_eq_one hε, one_mul]

theorem integral_mollifierEps_sq_le
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x : E, (mollifierEps hε x) ^ 2) ≤
      ((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) /
        ε ^ d := by
  convert integral_mollifierEps_sq_le_inv_volume_innerBall (d := d) hε using 1
  rw [Measure.addHaar_real_closedBall' volume (0 : E) (r := ε / 2) (by positivity)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, div_pow]
  field_simp

theorem mollifierEps_sq_bound_constant_pos :
    0 < (2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1) := by
  apply div_pos (by positivity)
  exact ENNReal.toReal_pos (measure_closedBall_pos volume (0 : E) zero_lt_one).ne'
    measure_closedBall_lt_top.ne

theorem integral_mollifierEps_sub_sq_le
    {ε : ℝ} (hε : 0 < ε) (y : E) :
    (∫ x : E, (mollifierEps hε (y - x)) ^ 2) ≤
      ((2 : ℝ) ^ d / (volume : Measure E).real (closedBall (0 : E) 1)) /
        ε ^ d := by
  rw [integral_sub_left_eq_self (fun x : E => (mollifierEps hε x) ^ 2) volume y]
  exact integral_mollifierEps_sq_le hε

theorem tsupport_mollifierEps_convolution_subset_cthickening
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {u : E → ℝ} {K : Set E}
    (hu : tsupport u ⊆ K) :
    tsupport (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) ⊆
      cthickening R K := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    Set.mem_add.mp (support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ) hx)
  have hzε : ‖z‖ ≤ ε := by
    simpa using mollifierEps_support_subset_closedBall_eps hε hz
  apply mem_cthickening_of_dist_le (y + z) y R K (hu (subset_tsupport u hy))
  simpa [dist_eq_norm] using hzε.trans hεR

theorem indicator_cthickening_mollifierEps_convolution
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {u : E → ℝ} {K : Set E}
    (hu : tsupport u ⊆ K) :
    (cthickening R K).indicator
      (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) =
      (mollifierEps hε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
  apply Set.indicator_eq_self.2
  exact (subset_tsupport _).trans
    (tsupport_mollifierEps_convolution_subset_cthickening hε hεR hu)

end Poincare.Analysis.Spectral.Counting
