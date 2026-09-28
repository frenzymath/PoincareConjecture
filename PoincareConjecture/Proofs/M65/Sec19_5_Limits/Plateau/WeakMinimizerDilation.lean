import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLocalization
import PoincareConjecture.Proofs.M03.Existence.ChartLpNative
import PoincareConjecture.Proofs.M03.Existence.ChartPullbackEnergyNative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap ENNReal

namespace PoincareConjecture

private theorem m65Dilation_map_le {r : ℝ} (hr : 1 / 2 ≤ r) :
    (volume.restrict loopDiskSet).map (fun z : LoopPlane => r • z) ≤
      (4 : ℝ≥0∞) • (volume : Measure LoopPlane) := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  apply (Measure.map_mono Measure.restrict_le_self (measurable_const_smul r)).trans
  rw [Measure.map_addHaar_smul volume hrpos.ne']
  have hcoef : ENNReal.ofReal |(r ^ 2)⁻¹| ≤ 4 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))]
    have hsq : (1 : ℝ) / 4 ≤ r ^ 2 := by nlinarith
    have hi : (r ^ 2)⁻¹ ≤ (4 : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ (sq_pos_of_pos hrpos)]
      nlinarith
    exact (ENNReal.ofReal_le_ofReal hi).trans_eq (by norm_num)
  apply Measure.le_iff.mpr
  intro s _
  simpa only [Measure.smul_apply, smul_eq_mul,
    finrank_euclideanSpace, Fintype.card_fin] using
      mul_le_mul_of_nonneg_right hcoef (show 0 ≤ volume s from bot_le)

noncomputable def m65DiskDilationL2 (r : ℝ) (hr : 1 / 2 ≤ r) :
    Lp ℝ 2 (volume : Measure LoopPlane) →L[ℝ]
      Lp ℝ 2 (volume.restrict loopDiskSet) :=
  ChartLpNative.dominatedPullbackL2 (fun z : LoopPlane => r • z)
    (measurable_const_smul r).aemeasurable (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    (m65Dilation_map_le hr)

theorem m65DiskDilationL2_coe (r : ℝ) (hr : 1 / 2 ≤ r)
    (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
    m65DiskDilationL2 r hr w =ᵐ[volume.restrict loopDiskSet]
      fun z => w (r • z) :=
  ChartLpNative.dominatedPullbackL2_coe _ _ _ _ w

theorem m65DiskDilationL2_norm_le (r : ℝ) (hr : 1 / 2 ≤ r)
    (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
    ‖m65DiskDilationL2 r hr w‖ ≤ 2 * ‖w‖ := by
  have hh := ChartLpNative.norm_dominatedPullbackL2_apply_le
    (fun z : LoopPlane => r • z) (measurable_const_smul r).aemeasurable
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) (m65Dilation_map_le hr) w
  norm_num [← Real.sqrt_eq_rpow] at hh ⊢
  exact hh

set_option maxHeartbeats 1600000 in

private theorem m65DiskDilationL2_schwartz
    (r : ℕ → ℝ) (hr : ∀ n, 1 / 2 ≤ r n) (hrlim : Tendsto r atTop (𝓝 1))
    (f : 𝓢(LoopPlane, ℝ)) :
    Tendsto (fun n => m65DiskDilationL2 (r n) (hr n) (f.toLp 2 volume)) atTop
      (𝓝 (m65DiskDilationL2 1 (by norm_num) (f.toLp 2 volume))) := by
  let mu : Measure LoopPlane := volume.restrict loopDiskSet
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall (0 : LoopPlane) 1).measure_lt_top.ne
  let U (n : ℕ) := m65DiskDilationL2 (r n) (hr n) (f.toLp 2 volume)
  let U0 := m65DiskDilationL2 1 (by norm_num) (f.toLp 2 volume)
  have hU (n : ℕ) : U n =ᵐ[mu] fun z => f (r n • z) := by
    apply (m65DiskDilationL2_coe (r n) (hr n) (f.toLp 2 volume)).trans
    exact ae_restrict_of_ae ((Measure.quasiMeasurePreserving_smul volume
      (ne_of_gt (lt_of_lt_of_le (by norm_num) (hr n)))).ae (f.coeFn_toLp 2 volume))
  have hU0 : U0 =ᵐ[mu] f := by
    have hh := m65DiskDilationL2_coe 1 (by norm_num) (f.toLp 2 volume)
    simp only [one_smul] at hh
    exact hh.trans (ae_restrict_of_ae (f.coeFn_toLp 2 volume))
  let C := SchwartzMap.seminorm ℝ 0 0 f
  have hC : 0 ≤ C := apply_nonneg _ _
  have hbound (n : ℕ) (z : LoopPlane) :
      ‖(f (r n • z) - f z) ^ 2‖ ≤ (2 * C) ^ 2 := by
    rw [norm_pow]
    have h := (norm_sub_le (f (r n • z)) (f z)).trans
      (add_le_add (f.norm_le_seminorm ℝ _) (f.norm_le_seminorm ℝ _))
    nlinarith [norm_nonneg (f (r n • z) - f z)]
  have hlim : ∀ᵐ z ∂mu, Tendsto (fun n => (f (r n • z) - f z) ^ 2) atTop (𝓝 0) := by
    filter_upwards [] with z
    have hc := (f.continuous.continuousAt.tendsto).comp
      (hrlim.smul_const z)
    simpa only [one_smul, sub_self, zero_pow (by decide : 2 ≠ 0), Function.comp_def] using
      (hc.sub_const (f z)).pow 2
  have hI := tendsto_integral_of_dominated_convergence (fun _ : LoopPlane => (2 * C) ^ 2)
    (fun n => ((f.continuous.comp (continuous_const_smul (r n))).sub f.continuous).pow
      2 |>.aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (hbound n)) hlim
  simp only [Pi.pow_apply, Pi.sub_apply, integral_zero] at hI
  have heq (n : ℕ) : ‖U n - U0‖ ^ 2 = ∫ z, (f (r n • z) - f z) ^ 2 ∂mu := by
    rw [ChartLpNative.scalarL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U n) U0, hU n, hU0] with z hz hn h0
    simp only [hz, Pi.sub_apply, hn, h0]
  have hn : Tendsto (fun n => ‖U n - U0‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hI
    simpa only [integral_zero, ← heq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
      Function.comp_def] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

theorem m65DiskDilationL2_tendsto
    (r : ℕ → ℝ) (hr : ∀ n, 1 / 2 ≤ r n) (hrlim : Tendsto r atTop (𝓝 1))
    (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
    Tendsto (fun n => m65DiskDilationL2 (r n) (hr n) w) atTop
      (𝓝 (m65DiskDilationL2 1 (by norm_num) w)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨f, hf⟩ := (SchwartzMap.denseRange_toLpCLM (E := LoopPlane) (F := ℝ)
    (μ := volume) (p := 2) (by norm_num)).exists_dist_lt w (by positivity : 0 < eps / 8)
  have hflim := m65DiskDilationL2_schwartz r hr hrlim f
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hflim (eps / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  let T := m65DiskDilationL2 (r n) (hr n)
  let T0 := m65DiskDilationL2 1 (by norm_num)
  have hdist (A : Lp ℝ 2 (volume : Measure LoopPlane) →L[ℝ]
      Lp ℝ 2 (volume.restrict loopDiskSet))
      (hA : ∀ v, ‖A v‖ ≤ 2 * ‖v‖) : dist (A w) (A (f.toLp 2 volume)) < eps / 4 := by
    rw [dist_eq_norm, ← map_sub]
    apply (hA _).trans_lt
    change dist w (f.toLp 2 volume) < eps / 8 at hf
    rw [dist_eq_norm] at hf
    linarith
  have hleft := hdist T (m65DiskDilationL2_norm_le _ _)
  have hright := hdist T0 (m65DiskDilationL2_norm_le _ _)
  have hmid := hN n hn
  have htri := dist_triangle4 (T w) (T (f.toLp 2 volume))
    (T0 (f.toLp 2 volume)) (T0 w)
  rw [dist_comm (T0 (f.toLp 2 volume)) (T0 w)] at htri
  exact htri.trans_lt (by linarith)

end PoincareConjecture
