import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryMeasure
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

noncomputable def m65CrosscutAngle (r : ℝ) : ℝ := Real.arccos (r / 2)

theorem m65Crosscut_mem_disk {r t : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (ht : t ∈ Icc (-m65CrosscutAngle r) (m65CrosscutAngle r)) :
    M65Interior.polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0) (r, t) ∈ loopDiskSet := by
  have harg0 : -1 ≤ r / 2 := by linarith
  have harg1 : r / 2 ≤ 1 := by linarith
  have hcos : r / 2 ≤ Real.cos t := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (Real.arccos_le_pi (r / 2)) (abs_le.mpr ht)
    simpa only [m65CrosscutAngle, Real.cos_abs,
      Real.cos_arccos harg0 harg1] using hc
  apply mem_closedBall_zero_iff.mpr
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, one_pow]
  simp [M65Interior.polarPlane, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
  nlinarith [congrArg (fun x : ℝ => r ^ 2 * x) (Real.sin_sq_add_cos_sq t),
    mul_nonneg hr.le (sub_nonneg.mpr hcos)]

theorem m65Crosscut_endpoint {r σ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hσ : σ = 1 ∨ σ = -1) :
    M65Interior.polarPlane (-EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (r, σ * m65CrosscutAngle r) =
        Proofs.M58.angularPoint (σ * (2 * m65CrosscutAngle r)) := by
  have hc : Real.cos (m65CrosscutAngle r) = r / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  rcases hσ with rfl | rfl <;> ext i <;> fin_cases i <;>
    simp [M65Interior.polarPlane, Proofs.M58.angularPoint,
      EuclideanSpace.basisFun_apply,
      Real.cos_two_mul, Real.sin_two_mul, hc] <;> ring

private theorem m65Crosscut_angle_map_le {ε R σ : ℝ} (hε : 0 < ε) (hR : R ≤ 1)
    (hσ : σ = 1 ∨ σ = -1) :
    (volume.restrict (Icc ε R)).map (fun r => σ * (2 * m65CrosscutAngle r)) ≤
      volume.restrict (Icc (-Real.pi) Real.pi) := by
  let a (r : ℝ) := σ * (2 * m65CrosscutAngle r)
  let da (r : ℝ) := σ * (-(1 / Real.sqrt (1 - (r / 2) ^ 2)))
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hda (r : ℝ) (hr : r ∈ Icc ε R) : HasDerivAt a (da r) r := by
    have ha : r / 2 ≠ -1 := by linarith [hr.1]
    have hb : r / 2 ≠ 1 := by linarith [hr.2]
    have hh := (((Real.hasDerivAt_arccos ha hb).comp r
      ((hasDerivAt_id r).div_const 2)).const_mul 2).const_mul σ
    have he : σ * (2 * (-(1 / Real.sqrt (1 - (r / 2) ^ 2)) * (1 / 2))) = da r := by
      dsimp only [da]
      ring
    rw [he] at hh
    exact hh
  have hai : InjOn a (Icc ε R) := by
    intro r hr s hs heq
    have hac : Real.arccos (r / 2) = Real.arccos (s / 2) := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
      exact mul_left_cancel₀ hσne heq
    have he := Real.arccos_injOn
      (show r / 2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hr.1], by linarith [hr.2]⟩)
      (show s / 2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hs.1], by linarith [hs.2]⟩) hac
    linarith
  have ha : Continuous a :=
    continuous_const.mul (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_id.div_const 2)))
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar volume
    measurableSet_Icc.nullMeasurableSet
    (fun r hr => (hda r hr).hasFDerivAt.hasFDerivWithinAt) hai
  have hweight : volume.restrict (Icc ε R) ≤
      (volume.restrict (Icc ε R)).withDensity (fun r => ENNReal.ofReal |da r|) := by
    calc
      _ = (volume.restrict (Icc ε R)).withDensity (fun _ => (1 : ℝ≥0∞)) :=
        withDensity_one.symm
      _ ≤ _ := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hsq : 0 < 1 - (r / 2) ^ 2 := by nlinarith [hr.1, hr.2]
        have hspos := Real.sqrt_pos.mpr hsq
        have hsle : Real.sqrt (1 - (r / 2) ^ 2) ≤ 1 := by
          apply (Real.sqrt_le_iff).mpr
          exact ⟨zero_le_one, by nlinarith [sq_nonneg (r / 2)]⟩
        have hdale : 1 ≤ |da r| := by
          dsimp only [da]
          rw [abs_mul, hσabs, one_mul, abs_neg, abs_div, abs_one,
            abs_of_pos hspos]
          exact (le_div_iff₀ hspos).mpr (by simpa using hsle)
        exact (ENNReal.ofReal_le_ofReal hdale).trans_eq' (by norm_num)
  have himage : a '' Icc ε R ⊆ Icc (-Real.pi) Real.pi := by
    rintro _ ⟨r, hr, rfl⟩
    have hc0 := Real.arccos_nonneg (r / 2)
    have hc1 := (Real.arccos_le_pi_div_two).mpr (show 0 ≤ r / 2 by linarith [hr.1])
    rcases hσ with rfl | rfl <;> dsimp only [a, m65CrosscutAngle] <;>
      constructor <;> nlinarith [Real.pi_pos]
  have hbound := Measure.map_mono hweight ha.measurable
  simp only [ContinuousLinearMap.det_toSpanSingleton] at hmap
  exact hbound.trans (hmap ▸ Measure.restrict_mono himage le_rfl)

noncomputable def m65CrosscutBoundaryL2 {ε R σ : ℝ}
    (hε : 0 < ε) (hR : R ≤ 1) (hσ : σ = 1 ∨ σ = -1) :
    Lp ℝ 2 m65CircleBoundaryMeasure →L[ℝ] Lp ℝ 2 (volume.restrict (Icc ε R)) :=
  (ChartLpNative.dominatedPullbackL2 (fun r => σ * (2 * m65CrosscutAngle r))
    (continuous_const.mul (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_id.div_const 2)))).measurable.aemeasurable
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (by simpa only [one_smul] using m65Crosscut_angle_map_le hε hR hσ)).comp
      m65CircleBoundaryPullback.toContinuousLinearMap

theorem m65CrosscutBoundaryL2_coe {ε R σ : ℝ}
    (hε : 0 < ε) (hR : R ≤ 1) (hσ : σ = 1 ∨ σ = -1)
    (b : Lp ℝ 2 m65CircleBoundaryMeasure) :
    m65CrosscutBoundaryL2 hε hR hσ b =ᵐ[volume.restrict (Icc ε R)]
      fun r => b (Proofs.M58.angularPoint (σ * (2 * m65CrosscutAngle r))) := by
  have ha : Measurable (fun r => σ * (2 * m65CrosscutAngle r)) :=
    (continuous_const.mul (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_id.div_const 2)))).measurable
  have hc := ChartLpNative.dominatedPullbackL2_coe
    (fun r => σ * (2 * m65CrosscutAngle r)) ha.aemeasurable
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (by simpa only [one_smul] using m65Crosscut_angle_map_le hε hR hσ)
    (m65CircleBoundaryPullback b)
  apply hc.trans
  exact ae_of_ae_map ha.aemeasurable
    (ae_mono (m65Crosscut_angle_map_le hε hR hσ) (m65CircleBoundaryPullback_coe b))

theorem m65CrosscutBoundaryL2_ae_of_ae {ε R σ : ℝ}
    (hε : 0 < ε) (hR : R ≤ 1) (hσ : σ = 1 ∨ σ = -1)
    (b : Lp ℝ 2 m65CircleBoundaryMeasure) (f : LoopPlane → ℝ)
    (hbf : b =ᵐ[m65CircleBoundaryMeasure] f) :
    m65CrosscutBoundaryL2 hε hR hσ b =ᵐ[volume.restrict (Icc ε R)]
      fun r => f (Proofs.M58.angularPoint (σ * (2 * m65CrosscutAngle r))) := by
  apply (m65CrosscutBoundaryL2_coe hε hR hσ b).trans
  have ha : Measurable (fun r => σ * (2 * m65CrosscutAngle r)) :=
    (continuous_const.mul (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_id.div_const 2)))).measurable
  exact ae_of_ae_map ha.aemeasurable
    (ae_mono (m65Crosscut_angle_map_le hε hR hσ)
      (ae_of_ae_map Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable hbf))

end PoincareConjecture
