import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPotential
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeightedPotential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric











set_option autoImplicit false

open Set MeasureTheory Complex Filter
open scoped Topology ContDiff SchwartzMap LineDeriv

namespace PoincareConjecture.M65Boundary

open M65Branch

private theorem complex_test_mixed (φ : 𝓢(ℂ, ℂ)) (v w : ℂ) :
    ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext z
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((φ.smooth 2).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  change fderiv ℝ (fun y => fderiv ℝ φ y w) z v =
    fderiv ℝ (fun y => fderiv ℝ φ y v) z w
  rw [fderiv_clm_apply hD (differentiableAt_const w),
    fderiv_clm_apply hD (differentiableAt_const v)]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_fun_const, Pi.zero_apply,
    zero_apply, map_zero, zero_add]
  exact ((φ.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w

private theorem test_derivative_support (φ : 𝓢(ℂ, ℂ)) (v : ℂ)
    (hφ : HasCompactSupport φ) : HasCompactSupport (∂_{v} φ : 𝓢(ℂ, ℂ)) :=
  hφ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset v φ)





theorem weak_laplacian_complex_gradient {u dx dy f : ℂ → ℂ} {U : Set ℂ}
    (hx : LocallyIntegrable dx volume) (hy : LocallyIntegrable dy volume)
    (hweak : ∀ φ : 𝓢(ℂ, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, φ z * dx z) = -(∫ z, fderiv ℝ φ z 1 * u z) ∧
      (∫ z, φ z * dy z) = -(∫ z, fderiv ℝ φ z I * u z))
    (heq : ∀ φ : 𝓢(ℂ, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, fderiv ℝ φ z 1 * dx z + fderiv ℝ φ z I * dy z) =
        -(∫ z, φ z * f z))
    (φ : 𝓢(ℂ, ℂ)) (hφ : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    (∫ z, dbar φ z * (dx z - I * dy z)) =
      -(∫ z, φ z * ((2 : ℂ)⁻¹ * f z)) := by
  let px := ∂_{(1 : ℂ)} φ
  let py := ∂_{I} φ
  have hpxs := SchwartzMap.tsupport_lineDerivOp_subset (1 : ℂ) φ
  have hpys := SchwartzMap.tsupport_lineDerivOp_subset I φ
  have hxy := (hweak py (test_derivative_support φ I hφ) (hpys.trans hs)).1
  have hyx := (hweak px (test_derivative_support φ 1 hφ) (hpxs.trans hs)).2
  have hcomm (z : ℂ) : fderiv ℝ py z 1 = fderiv ℝ px z I := by
    exact congrArg (fun ψ : 𝓢(ℂ, ℂ) => ψ z) (complex_test_mixed φ 1 I)
  simp_rw [hcomm] at hxy
  have hcurl : (∫ z, fderiv ℝ φ z I * dx z) =
      (∫ z, fderiv ℝ φ z 1 * dy z) := hxy.trans hyx.symm
  have hi (v : ℂ) (d : ℂ → ℂ) (hd : LocallyIntegrable d volume) :
      Integrable (fun z => fderiv ℝ φ z v * d z) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul] using
      hd.integrable_smul_left_of_hasCompactSupport
        (∂_{v} φ : 𝓢(ℂ, ℂ)).continuous (test_derivative_support φ v hφ)
  have hpoint (z : ℂ) : dbar φ z * (dx z - I * dy z) =
      (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 * dx z + fderiv ℝ φ z I * dy z) +
        ((2 : ℂ)⁻¹ * I) * (fderiv ℝ φ z I * dx z - fderiv ℝ φ z 1 * dy z) := by
    simp only [dbar, dbarLinear, smul_eq_mul, add_apply, smul_apply,
      ContinuousLinearMap.apply_apply]
    calc
      _ = (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 * dx z - I ^ 2 *
          (fderiv ℝ φ z I * dy z)) +
          ((2 : ℂ)⁻¹ * I) * (fderiv ℝ φ z I * dx z - fderiv ℝ φ z 1 * dy z) := by ring
      _ = _ := by rw [I_sq]; ring
  simp_rw [hpoint]
  rw [integral_add (f := fun z => (2 : ℂ)⁻¹ *
      (fderiv ℝ φ z 1 * dx z + fderiv ℝ φ z I * dy z))
    (g := fun z => ((2 : ℂ)⁻¹ * I) *
      (fderiv ℝ φ z I * dx z - fderiv ℝ φ z 1 * dy z))
    (((hi 1 dx hx).add (hi I dy hy)).const_mul _)
    (((hi I dx hx).sub (hi 1 dy hy)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub (hi I dx hx) (hi 1 dy hy), hcurl, sub_self, mul_zero, add_zero,
    heq φ hφ hs]
  calc
    _ = -(∫ z, (2 : ℂ)⁻¹ * (φ z * f z)) := by rw [integral_const_mul]; ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      ring




theorem weak_gradient_cauchy_decomposition {u dx dy f : ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hx : LocallyIntegrable dx volume) (hy : LocallyIntegrable dy volume)
    (hf : Integrable f) (hs : Function.support f ⊆ Metric.closedBall (0 : ℂ) R)
    (hU : IsOpen U)
    (hweak : ∀ φ : 𝓢(ℂ, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, φ z * dx z) = -(∫ z, fderiv ℝ φ z 1 * u z) ∧
      (∫ z, φ z * dy z) = -(∫ z, fderiv ℝ φ z I * u z))
    (heq : ∀ φ : 𝓢(ℂ, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, fderiv ℝ φ z 1 * dx z + fderiv ℝ φ z I * dy z) =
        -(∫ z, φ z * f z))
    {x : ℂ} (hxU : x ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧
      DifferentiableOn ℂ H (Metric.ball x r) ∧
      ∀ᵐ z ∂volume.restrict (Metric.ball x r),
        dx z - I * dy z = cauchyOperator (fun w => (2 : ℂ)⁻¹ * f w) z + H z := by
  have hW : LocallyIntegrable (fun z => dx z - I * dy z) volume := by
    simpa +instances only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using! hx.sub (hy.smul I)
  apply exists_cauchy_decomposition hW (hf.const_mul _)
    (R := R) _ hU _ hxU
  · intro z hz
    apply hs
    intro hf0
    exact hz (by simp only [hf0, mul_zero])
  · exact weak_laplacian_complex_gradient hx hy hweak heq

private theorem translated_weight_ball {b R : ℝ} (hb : b < 2) (x : ℂ) :
    IntegrableOn (fun z : ℂ => ‖x - z‖ ^ (-b)) (Metric.ball x R) ∧
      (∫ z in Metric.ball x R, ‖x - z‖ ^ (-b)) =
        ∫ z in Metric.ball (0 : ℂ) R, ‖z‖ ^ (-b) := by
  classical
  have hi : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-b)) (Metric.ball 0 R) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (C := 1) (α := b) (by simpa using hb)
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
    · apply Measurable.aestronglyMeasurable
      fun_prop
  let k := (Metric.ball (0 : ℂ) R).indicator (fun z : ℂ => ‖z‖ ^ (-b))
  have hk : Integrable k := hi.integrable_indicator measurableSet_ball
  have hsame (z : ℂ) : k (x - z) =
      (Metric.ball x R).indicator (fun w : ℂ => ‖x - w‖ ^ (-b)) z := by
    have hm : x - z ∈ Metric.ball (0 : ℂ) R ↔ z ∈ Metric.ball x R := by
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
    change (if x - z ∈ Metric.ball (0 : ℂ) R then ‖x - z‖ ^ (-b) else 0) = _
    rw [hm]
    rfl
  have htrans : Integrable (fun z => k (x - z)) :=
    (Measure.measurePreserving_sub_left volume x).integrable_comp_emb
      (Homeomorph.subLeft x).measurableEmbedding |>.mpr hk
  constructor
  · rw [← integrable_indicator_iff measurableSet_ball]
    exact htrans.congr (ae_of_all _ hsame)
  · rw [← integral_indicator measurableSet_ball,
      ← integral_indicator measurableSet_ball]
    calc
      _ = ∫ z, k (x - z) := integral_congr_ae (ae_of_all _ fun z => (hsame z).symm)
      _ = ∫ z, k z := integral_sub_left_eq_self k volume x





theorem weak_gradient_weighted_estimate {b : ℝ} (hb : 1 < b) (hb2 : b < 2)
    {W h : ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hW : LocallyIntegrable W volume) (hh : Integrable h)
    (hs : Function.support h ⊆ Metric.closedBall (0 : ℂ) R) (hU : IsOpen U)
    (hweak : ∀ ψ : 𝓢(ℂ, ℂ), HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ z, dbar ψ z * W z) = -(∫ z, ψ z * h z))
    {p : ℂ} (hp : p ∈ U) :
    ∃ r > 0, ∃ A ≥ 0, ∃ C > 0, ∀ x ∈ Metric.ball p r,
      Integrable (fun w => ‖h w‖ * ‖w - x‖ ^ (1 - b)) →
      IntegrableOn (fun z => ‖x - z‖ ^ (-b) * ‖W z‖) (Metric.ball p r) ∧
      (∫ z in Metric.ball p r, ‖x - z‖ ^ (-b) * ‖W z‖) ≤
        A + C * ∫ w, ‖h w‖ * ‖w - x‖ ^ (1 - b) := by
  obtain ⟨r, hr, H, hH, _hhol, heq⟩ := exists_cauchy_decomposition hW hh hs hU hweak hp
  obtain ⟨C, hC, hpot⟩ := weighted_cauchy_estimate hb hb2
  obtain ⟨B, hB⟩ := (isCompact_closedBall p (r / 2)).bddAbove_image
    hH.continuous.norm.continuousOn
  let B' := max B 0
  let K := ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-b)
  have hK : 0 ≤ K := integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg z) _
  refine ⟨r / 2, by positivity, B' * K, mul_nonneg (le_max_right _ _) hK, C, hC, ?_⟩
  intro x hx hw
  have hsub : Metric.ball p (r / 2) ⊆ Metric.ball x r := by
    intro z hz
    have hx' := Metric.mem_ball.mp hx
    have hz' := Metric.mem_ball.mp hz
    apply Metric.mem_ball.mpr
    calc
      dist z x ≤ dist z p + dist p x := dist_triangle _ _ _
      _ < r := by rw [dist_comm p x]; linarith
  obtain ⟨hki, hke⟩ := translated_weight_ball hb2 x (R := r)
  have hkis := hki.mono_set hsub
  have hkbound : (∫ z in Metric.ball p (r / 2), ‖x - z‖ ^ (-b)) ≤ K := by
    dsimp only [K]
    rw [← hke]
    apply setIntegral_mono_set hki
      (ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg _) _) hsub.eventuallyLE
  obtain ⟨hpi, hpe⟩ := hpot h x hh.aestronglyMeasurable hw
  have hHi : IntegrableOn (fun z => ‖x - z‖ ^ (-b) * ‖H z‖)
      (Metric.ball p (r / 2)) := by
    apply Integrable.mul_bdd (c := B') hkis hH.continuous.norm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [Real.norm_eq_abs, abs_norm]
    exact (hB ⟨z, Metric.ball_subset_closedBall hz, rfl⟩).trans (le_max_left B 0)
  have hHbound : (∫ z in Metric.ball p (r / 2), ‖x - z‖ ^ (-b) * ‖H z‖) ≤ B' * K := by
    calc
      _ ≤ ∫ z in Metric.ball p (r / 2), ‖x - z‖ ^ (-b) * B' := by
        apply integral_mono_ae hHi (hkis.mul_const B')
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact mul_le_mul_of_nonneg_left
          ((hB ⟨z, Metric.ball_subset_closedBall hz, rfl⟩).trans (le_max_left B 0))
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = B' * ∫ z in Metric.ball p (r / 2), ‖x - z‖ ^ (-b) := by
        rw [integral_mul_const, mul_comm]
      _ ≤ B' * K := mul_le_mul_of_nonneg_left hkbound (le_max_right _ _)
  have hsmall : Metric.ball p (r / 2) ⊆ Metric.ball p r :=
    Metric.ball_subset_ball (by linarith)
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball p (r / 2)),
      ‖x - z‖ ^ (-b) * ‖W z‖ ≤
        ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖ + ‖x - z‖ ^ (-b) * ‖H z‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall heq] with z hz
    rw [hz, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hWi : IntegrableOn (fun z => ‖x - z‖ ^ (-b) * ‖W z‖)
      (Metric.ball p (r / 2)) := by
    apply (hpi.integrableOn.add hHi).mono' ?_ ?_
    · exact ((by fun_prop : Measurable (fun z : ℂ => ‖x - z‖ ^ (-b))).aestronglyMeasurable.mul
        hW.aestronglyMeasurable.norm).restrict
    · filter_upwards [hbound] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
      exact hz
  refine ⟨hWi, ?_⟩
  calc
    _ ≤ ∫ z in Metric.ball p (r / 2),
        ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖ + ‖x - z‖ ^ (-b) * ‖H z‖ :=
      integral_mono_ae hWi (hpi.integrableOn.add hHi) hbound
    _ = (∫ z in Metric.ball p (r / 2), ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖) +
        ∫ z in Metric.ball p (r / 2), ‖x - z‖ ^ (-b) * ‖H z‖ :=
      integral_add hpi.integrableOn hHi
    _ ≤ (∫ z, ‖x - z‖ ^ (-b) * ‖cauchyOperator h z‖) + B' * K := by
      apply add_le_add _ hHbound
      exact setIntegral_le_integral hpi (ae_of_all _ fun z =>
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))
    _ ≤ _ := by linarith only [hpe]

end PoincareConjecture.M65Boundary
