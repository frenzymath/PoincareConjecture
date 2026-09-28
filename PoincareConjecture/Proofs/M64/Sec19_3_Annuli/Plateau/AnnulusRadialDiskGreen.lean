import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMapCircleGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.UniformCircleIntegral
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1
local notation "K" => closedBall (0 : LoopPlane) 1
local notation "mu" => volume.restrict S

theorem m64WeakDisk_good_radius
    (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => u p b) S)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ r ∈ Ioo t 1, ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in ball (0 : LoopPlane) r, phi p • V i p) +
        (∫ p in ball (0 : LoopPlane) r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) =
        r • ∫ x in Icc (-Real.pi) Real.pi,
          angularPoint x i • (phi (r • angularPoint x) • u (r • angularPoint x)) := by
  let rho := (t + 1) / 2
  have hrho : 0 < rho := by dsimp only [rho]; linarith
  have htrho : t < rho := by dsimp only [rho]; linarith
  have hrho1 : rho < 1 := by dsimp only [rho]; linarith
  have hKO : closedBall (0 : LoopPlane) rho ⊆ S :=
    closedBall_subset_ball hrho1
  have hg := m64WeakMap_local_circle_green isOpen_ball 0 hrho hKO u V hu hV hw
  let delta := (rho - t) / (2 * rho)
  have hd : 0 < delta := div_pos (sub_pos.mpr htrho) (by positivity)
  have hd1 : delta ≤ 1 := (div_le_one (by positivity : 0 < 2 * rho)).mpr (by linarith)
  have hsub : Ioo (0 : ℝ) delta ⊆ Icc (0 : ℝ) 1 :=
    fun _ hs => ⟨hs.1.le, hs.2.le.trans hd1⟩
  obtain ⟨s, hs, hgreen⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo (0 : ℝ) delta) ≠ 0 by
      rw [Real.volume_Ioo, sub_zero]
      exact (ENNReal.ofReal_pos.mpr hd).ne')
    (ae_restrict_of_ae_restrict_of_subset hsub hg)
  let r := rho * Real.exp (-s)
  have hrs : t < r := by
    have hsd : 2 * rho * s < rho - t := by
      have hh := (lt_div_iff₀ (show 0 < 2 * rho by positivity)).mp hs.2
      nlinarith
    have hexp := Real.add_one_le_exp (-s)
    dsimp only [r]
    nlinarith
  have hr1 : r < 1 := (mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1.le))).trans_lt hrho1
  refine ⟨r, ⟨hrs, hr1⟩, ?_⟩
  intro phi hphi i
  have h := hgreen phi hphi i
  change (∫ p in closedBall (0 : LoopPlane) r, phi p • V i p) +
    (∫ p in closedBall (0 : LoopPlane) r,
      fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) =
      r • ∫ x in Icc (0 : ℝ) curvePeriod,
        angularPoint (x - Real.pi) i •
          (phi (0 + r • angularPoint (x - Real.pi)) • u (0 + r • angularPoint (x - Real.pi))) at h
  simp only [zero_add] at h
  rw [← m64CircleIntegral_shift (fun x => angularPoint x i •
    (phi (r • angularPoint x) • u (r • angularPoint x)))] at h
  rw [setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume (0 : LoopPlane) r),
    setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume (0 : LoopPlane) r)]
  exact h

theorem m64Disk_setIntegral_tendsto
    {r : ℕ → ℝ} (hr : ∀ j, r j ≤ 1) (hlim : Tendsto r atTop (𝓝 1))
    {f : LoopPlane → E} (hf : IntegrableOn f S volume) :
    Tendsto (fun j => ∫ p in ball (0 : LoopPlane) (r j), f p) atTop (𝓝 (∫ p in S, f p)) := by
  have hcover : AECover mu atTop (fun j => ball (0 : LoopPlane) (r j)) := {
    ae_eventually_mem := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      exact hlim.eventually (eventually_gt_nhds hp)
    measurableSet := fun _ => measurableSet_ball }
  have h := hcover.integral_tendsto_of_countably_generated hf
  have hrestrict (j : ℕ) : (mu).restrict (ball (0 : LoopPlane) (r j)) =
      volume.restrict (ball (0 : LoopPlane) (r j)) :=
    Measure.restrict_restrict_of_subset (ball_subset_ball (hr j))
  simpa only [hrestrict] using h

theorem m64Disk_radial_tendstoUniformly
    {r : ℕ → ℝ} (hlim : Tendsto r atTop (𝓝 1)) :
    TendstoUniformly (fun j t => r j • angularPoint t) angularPoint atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds (1 : ℝ) hepsilon)] with j hj
  intro t
  have heq : dist (angularPoint t) (r j • angularPoint t) = dist (r j) 1 := by
    have hs : angularPoint t - r j • angularPoint t = (1 - r j) • angularPoint t := by
      rw [sub_smul, one_smul]
    rw [dist_eq_norm, hs, norm_smul,
      norm_angularPoint, mul_one, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm]
  exact heq.trans_lt hj

set_option maxHeartbeats 800000 in

theorem m64ContinuousH1Disk_green
    (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
    (hu : MemLp u 2 mu) (hV : ∀ i, MemLp (V i) 2 mu)
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => u p b) S)
    (hc : ContinuousOn u K) (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in S, phi p • V i p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) =
      ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • (phi (angularPoint t) • u (angularPoint t)) := by
  have hthreshold0 (j : ℕ) : 0 ≤ 1 - (1 / 2 : ℝ) ^ j :=
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  have hthreshold1 (j : ℕ) : 1 - (1 / 2 : ℝ) ^ j < 1 :=
    sub_lt_self _ (pow_pos (by norm_num) _)
  choose r hr hgreen using fun j =>
    m64WeakDisk_good_radius u V hu hV hw (hthreshold0 j) (hthreshold1 j)
  have hr0 (j : ℕ) : 0 ≤ r j := (hthreshold0 j).trans (hr j).1.le
  have hr1 (j : ℕ) : r j ≤ 1 := (hr j).2.le
  have hthreshold : Tendsto (fun j : ℕ => 1 - (1 / 2 : ℝ) ^ j) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hrlim : Tendsto r atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hthreshold tendsto_const_nhds
      (fun j => (hr j).1.le) hr1
  let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hdc : Continuous dphi := (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp : MemLp phi 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hdp : MemLp dphi 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm hdc.aestronglyMeasurable).mpr
    exact (hdc.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hInt {f : LoopPlane → ℝ} {v : LoopPlane → E} (hf : MemLp f 2 mu) (hv : MemLp v 2 mu) :
      Integrable (fun p => f p • v p) mu := by
    apply (hf.norm.integrable_mul hv.norm).mono'
      (hf.aestronglyMeasurable.smul hv.aestronglyMeasurable)
    exact Eventually.of_forall (fun p => (norm_smul (f p) (v p)).le)
  have hleft := (m64Disk_setIntegral_tendsto hr1 hrlim (hInt hp (hV i))).add
    (m64Disk_setIntegral_tendsto hr1 hrlim (hInt hdp hu))
  let G := fun p => phi p • u p
  have hGc : ContinuousOn G K := hphi.continuous.continuousOn.smul hc
  have hGuni := (isCompact_closedBall (0 : LoopPlane) 1).uniformContinuousOn_of_continuous hGc
  have hmap (j : ℕ) (t : ℝ) : r j • angularPoint t ∈ K := by
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_angularPoint, mul_one,
      Real.norm_of_nonneg (hr0 j)]
    exact hr1 j
  have hangle (t : ℝ) : angularPoint t ∈ K := by
    simp only [mem_closedBall, dist_zero_right, norm_angularPoint, le_refl]
  have hGlim : TendstoUniformlyOn (fun j t => G (r j • angularPoint t))
      (fun t => G (angularPoint t)) atTop (Icc (-Real.pi) Real.pi) :=
    hGuni.comp_tendstoUniformlyOn_eventually
      (Eventually.of_forall fun j t _ => hmap j t) (fun t _ => hangle t)
      (m64Disk_radial_tendstoUniformly hrlim).tendstoUniformlyOn
  have hGcj (j : ℕ) : ContinuousOn (fun t => G (r j • angularPoint t))
      (Icc (-Real.pi) Real.pi) :=
    hGc.comp (contDiff_angularPoint.continuous.const_smul (r j)).continuousOn
      (fun t _ => hmap j t)
  have hweight : Continuous (fun t : ℝ => angularPoint t i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp contDiff_angularPoint.continuous
  have hright := hrlim.smul (m64UniformCircle_weighted_integral_tendsto
    (neg_le_self Real.pi_pos.le) hGcj hGlim (fun t => angularPoint t i) hweight.continuousOn)
  simp only [one_smul] at hright
  exact tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun j => (hgreen j phi hphi i).symm))

end PoincareConjecture
