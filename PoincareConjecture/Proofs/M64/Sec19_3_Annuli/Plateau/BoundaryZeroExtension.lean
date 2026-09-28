import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroTraceCutoff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

theorem m64Continuous_zeroExtension_continuous {u : LoopPlane → ℝ}
    (hu : Continuous u) (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0) :
    Continuous ((halfSpace 2).indicator u) := by
  have heq : (halfSpace 2).indicator u = m64ContinuousBoundaryReflect 0 u := by
    funext p
    by_cases hp : 0 < p 0
    · simp [halfSpace, m64ContinuousBoundaryReflect, hp, hp.le]
    · by_cases hz : p 0 = 0
      · simp [halfSpace, m64ContinuousBoundaryReflect, hz, hzero p hz]
      · have hn : p 0 < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
        simp [halfSpace, m64ContinuousBoundaryReflect, hp, not_le.mpr hn]
  rw [heq]
  exact m64ContinuousBoundaryReflect_continuous hu 0
    (fun p hp => by rw [hzero p hp, mul_zero])

private theorem integral_normalCutoff_tendsto {a : LoopPlane → ℝ}
    (ha : Integrable a (volume.restrict (halfSpace 2))) :
    Tendsto (fun n => ∫ p in halfSpace 2, normalCutoff n p * a p) atTop
      (𝓝 (∫ p in halfSpace 2, a p)) := by
  apply tendsto_integral_of_dominated_convergence (fun p => ‖a p‖)
  · intro n
    exact ((normalCutoff_smooth n).continuous.aestronglyMeasurable.restrict).mul
      ha.aestronglyMeasurable
  · exact ha.norm
  · intro n
    exact Eventually.of_forall fun p => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (normalCutoff_norm_le n p) (norm_nonneg _))
        |>.trans_eq (one_mul _)
  · filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with p hp
    simpa using (normalCutoff_tendsto hp).mul_const (a p)

theorem m64Continuous_zeroTrace_weak_test {u v phi : LoopPlane → ℝ} (i : Fin 2)
    (hu : Continuous u)
    (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0)
    (huLp : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hvLp : MemLp v 2 (volume.restrict (halfSpace 2)))
    (hw : HasWeakPartialDeriv i v u (halfSpace 2))
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p in halfSpace 2, u p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      -(∫ p in halfSpace 2, v p * phi p) := by
  let dphi : LoopPlane → ℝ := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hdc : Continuous dphi := (hp.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcomp : HasCompactSupport dphi := hc.fderiv_apply (𝕜 := ℝ) _
  have hIu : Integrable (fun p => u p * dphi p) (volume.restrict (halfSpace 2)) :=
    huLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      |>.integrable_smul_right_of_hasCompactSupport hdc hdcomp
  have hIv : Integrable (fun p => v p * phi p) (volume.restrict (halfSpace 2)) :=
    hvLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      |>.integrable_smul_right_of_hasCompactSupport hp.continuous hc
  have herr : Tendsto (fun n => ∫ p in halfSpace 2,
      u p * phi p * fderiv ℝ (normalCutoff n) p (EuclideanSpace.single i 1))
      atTop (𝓝 0) := by
    by_cases hi : i = 0
    · subst i
      exact m64NormalCutoff_zeroTrace_error_tendsto (hu.mul hp.continuous) hc.mul_left
        (fun p hp0 => by rw [hzero p hp0, zero_mul])
    · simpa only [normalCutoff_partial _ _ hi, mul_zero, integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have heq (n : ℕ) :
      (∫ p in halfSpace 2, normalCutoff n p * (u p * dphi p)) +
        (∫ p in halfSpace 2,
          u p * phi p * fderiv ℝ (normalCutoff n) p (EuclideanSpace.single i 1)) =
        -(∫ p in halfSpace 2, normalCutoff n p * (v p * phi p)) := by
    have hleft : Integrable (fun p => normalCutoff n p * (u p * dphi p))
        (volume.restrict (halfSpace 2)) := by
      convert huLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        |>.integrable_smul_right_of_hasCompactSupport
          ((normalCutoff_smooth n).continuous.mul hdc) hdcomp.mul_left using 1
      ext p
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have herrI : Integrable (fun p =>
        u p * phi p * fderiv ℝ (normalCutoff n) p (EuclideanSpace.single i 1))
        (volume.restrict (halfSpace 2)) := by
      convert huLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        |>.integrable_smul_right_of_hasCompactSupport
          (hp.continuous.mul (((normalCutoff_smooth n).continuous_fderiv (by simp)).clm_apply
            (continuous_const (y := EuclideanSpace.single i 1))))
          hc.mul_right using 1
      ext p
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have hprod (p : LoopPlane) :
        fderiv ℝ (fun q => normalCutoff n q * phi q) p (EuclideanSpace.single i 1) =
          normalCutoff n p * dphi p +
            phi p * fderiv ℝ (normalCutoff n) p (EuclideanSpace.single i 1) := by
      have hd := (((normalCutoff_smooth n).differentiable (by simp) p).hasFDerivAt.mul
        (hp.differentiable (by simp) p).hasFDerivAt).fderiv
      simpa [dphi, Pi.mul_def] using
        congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd
    rw [← integral_add hleft herrI]
    calc
      _ = ∫ p in halfSpace 2, u p * fderiv ℝ
          (fun q => normalCutoff n q * phi q) p (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by dsimp only; rw [hprod]; ring
      _ = _ := hw _ ((normalCutoff_smooth n).mul hp) hc.mul_left
        (tsupport_mul_subset_left.trans (normalCutoff_tsupport n))
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by ring
  have hh := (integral_normalCutoff_tendsto hIu).add herr
  simpa only [add_zero] using tendsto_nhds_unique hh
    ((integral_normalCutoff_tendsto hIv).neg.congr'
      (Eventually.of_forall fun n => (heq n).symm))

theorem m64Continuous_zeroExtension_weak {u v : LoopPlane → ℝ} (i : Fin 2)
    (hu : Continuous u)
    (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0)
    (huLp : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hvLp : MemLp v 2 (volume.restrict (halfSpace 2)))
    (hw : HasWeakPartialDeriv i v u (halfSpace 2)) :
    HasWeakPartialDeriv i ((halfSpace 2).indicator v)
      ((halfSpace 2).indicator u) univ := by
  intro phi hp hc _
  simp only [Measure.restrict_univ]
  have hpair (f q : LoopPlane → ℝ) :
      (∫ p, (halfSpace 2).indicator f p * q p) =
        ∫ p in halfSpace 2, f p * q p := by
    rw [← integral_indicator isOpen_halfSpace.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      by_cases hh : p ∈ halfSpace 2 <;> simp [hh]
  rw [hpair, hpair]
  exact m64Continuous_zeroTrace_weak_test i hu hzero huLp hvLp hw hp hc

end PoincareConjecture
