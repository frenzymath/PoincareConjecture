import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakCR












set_option autoImplicit false

open Set Metric Filter MeasureTheory Complex
open scoped Topology ContDiff Convolution SchwartzMap

namespace PoincareConjecture.M65Boundary

open M65Branch

private theorem cauchy_truncation {h : ℂ → ℂ} {R S : ℝ}
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) S) :
    cauchyOperator h z = (Real.pi : ℂ)⁻¹ *
      (h ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (closedBall (0 : ℂ) (R + S)).indicator (fun w => w⁻¹)) z := by
  rw [cauchyOperator, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  change (z - w)⁻¹ * h w =
    h w * (closedBall (0 : ℂ) (R + S)).indicator (fun v => v⁻¹) (z - w)
  by_cases hw : h w = 0
  · rw [hw, mul_zero, zero_mul]
  · have hwr := mem_closedBall_zero_iff.mp (hs hw)
    have hzr := mem_closedBall_zero_iff.mp hz
    have hzw : z - w ∈ closedBall (0 : ℂ) (R + S) :=
      mem_closedBall_zero_iff.mpr ((norm_sub_le z w).trans (by linarith))
    rw [indicator_of_mem hzw, mul_comm]




theorem locallyIntegrable_cauchyOperator_L1 {h : ℂ → ℂ} {R : ℝ}
    (hh : Integrable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R) :
    LocallyIntegrable (cauchyOperator h) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨S, _hS, hKS⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
  let k := (closedBall (0 : ℂ) (R + S)).indicator (fun w : ℂ => w⁻¹)
  have hk : Integrable k volume :=
    (locallyIntegrable_cauchyKernel.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) (R + S))).integrable_indicator
      isClosed_closedBall.measurableSet
  have hconv := (hh.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hk).const_mul
    (Real.pi : ℂ)⁻¹
  apply hconv.integrableOn.congr
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact (cauchy_truncation hs (ball_subset_closedBall (hKS hz))).symm

private theorem cauchy_test_integrable {h : ℂ → ℂ} {R : ℝ}
    (hh : Integrable h volume) (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    Integrable (fun p : ℂ × ℂ => dbar φ p.1 * ((p.1 - p.2)⁻¹ * h p.2))
      (volume.prod volume) := by
  obtain ⟨S, _hS, hS⟩ := hφs.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  let k := (closedBall (0 : ℂ) (R + S)).indicator (fun w : ℂ => w⁻¹)
  have hk : Integrable k volume :=
    (locallyIntegrable_cauchyKernel.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) (R + S))).integrable_indicator
      isClosed_closedBall.measurableSet
  have hbase : Integrable (fun p : ℂ × ℂ => h p.2 * k (p.1 - p.2))
      (volume.prod volume) := hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hk
  have hbar := continuous_dbar hφ
  obtain ⟨B, hB⟩ := hbar.norm.bddAbove_range_of_hasCompactSupport
    (hasCompactSupport_dbar hφs).norm
  have hbound : ∀ᵐ p : ℂ × ℂ ∂volume.prod volume, ‖dbar φ p.1‖ ≤ B :=
    Eventually.of_forall fun p => hB ⟨p.1, rfl⟩
  have hi := hbase.mul_bdd (hbar.comp continuous_fst).aestronglyMeasurable hbound
  apply hi.congr
  filter_upwards [] with p
  dsimp only [Function.comp_apply]
  by_cases hh0 : h p.2 = 0
  · simp only [hh0, zero_mul, mul_zero]
  by_cases hφ0 : dbar φ p.1 = 0
  · simp only [hφ0, zero_mul, mul_zero]
  have hz : p.1 ∈ tsupport φ := by
    by_contra hnot
    apply hφ0
    change dbarLinear (fderiv ℝ φ p.1) = 0
    rw [fderiv_of_notMem_tsupport ℝ hnot, map_zero]
  have hzw : p.1 - p.2 ∈ closedBall (0 : ℂ) (R + S) := by
    have hwr := mem_closedBall_zero_iff.mp (hs hh0)
    have hzr := mem_ball_zero_iff.mp (hS hz)
    exact mem_closedBall_zero_iff.mpr ((norm_sub_le p.1 p.2).trans (by linarith))
  dsimp only [k]
  rw [indicator_of_mem hzw]
  ring





theorem cauchyOperator_L1_weak_dbar {h : ℂ → ℂ} {R : ℝ}
    (hh : Integrable h volume) (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    (∫ z, dbar φ z * cauchyOperator h z) = -(∫ z, φ z * h z) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv (w : ℂ) : (∫ z : ℂ, (z - w)⁻¹ * dbar φ z) =
      -(Real.pi : ℂ) * φ w := by
    have hactual := cauchyOperator_dbar hφ hφs w
    simp only [cauchyOperator, smul_eq_mul] at hactual
    have hJ : (∫ z : ℂ, (w - z)⁻¹ * dbar φ z) = (Real.pi : ℂ) * φ w := by
      calc
        _ = (Real.pi : ℂ) * ((Real.pi : ℂ)⁻¹ *
            (∫ z : ℂ, (w - z)⁻¹ * dbar φ z)) := by field_simp
        _ = _ := by rw [hactual]
    calc
      _ = -(∫ z : ℂ, (w - z)⁻¹ * dbar φ z) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with z
        rw [← neg_sub w z, inv_neg, neg_mul]
      _ = _ := by rw [hJ, neg_mul]
  have hpoint (z : ℂ) : dbar φ z * cauchyOperator h z =
      (Real.pi : ℂ)⁻¹ * ∫ w, dbar φ z * ((z - w)⁻¹ * h w) := by
    simp only [cauchyOperator, smul_eq_mul, integral_const_mul]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_integral_swap (cauchy_test_integrable hh hs hφ hφs)]
  have hinner (w : ℂ) : (∫ z, dbar φ z * ((z - w)⁻¹ * h w)) =
      -(Real.pi : ℂ) * (φ w * h w) := by
    calc
      _ = (∫ z : ℂ, (z - w)⁻¹ * dbar φ z) * h w := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = _ := by rw [hinv]; ring
  simp_rw [hinner]
  rw [integral_const_mul]
  field_simp





theorem exists_cauchy_decomposition {W h : ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hW : LocallyIntegrable W volume) (hh : Integrable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R) (hU : IsOpen U)
    (hweak : ∀ ψ : 𝓢(ℂ, ℂ), HasCompactSupport (ψ : ℂ → ℂ) →
      tsupport (ψ : ℂ → ℂ) ⊆ U →
        (∫ z, dbar ψ z * W z) = -(∫ z, ψ z * h z))
    {x : ℂ} (hx : x ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧ DifferentiableOn ℂ H (ball x r) ∧
      ∀ᵐ z ∂volume.restrict (ball x r), W z = cauchyOperator h z + H z := by
  let V := U ∩ ball x 1
  let D := closedBall x 2
  let F := D.indicator (fun z => W z - cauchyOperator h z)
  have hC := locallyIntegrable_cauchyOperator_L1 hh hs
  have hF : Integrable F volume :=
    ((hW.sub hC).integrableOn_isCompact (isCompact_closedBall x 2)).integrable_indicator
      isClosed_closedBall.measurableSet
  have hV : IsOpen V := hU.inter isOpen_ball
  have hxV : x ∈ V := ⟨hx, mem_ball_self (by norm_num)⟩
  have hFweak (ψ : 𝓢(ℂ, ℂ)) (hψ : HasCompactSupport (ψ : ℂ → ℂ))
      (hψV : tsupport (ψ : ℂ → ℂ) ⊆ V) : (∫ z, dbar ψ z * F z) = 0 := by
    have hd := continuous_dbar (ψ.smooth 1)
    have hds := hasCompactSupport_dbar hψ
    have hiW : Integrable (fun z => dbar ψ z * W z) volume := by
      simpa only [smul_eq_mul] using hW.integrable_smul_left_of_hasCompactSupport hd hds
    have hiC : Integrable (fun z => dbar ψ z * cauchyOperator h z) volume := by
      simpa only [smul_eq_mul] using hC.integrable_smul_left_of_hasCompactSupport hd hds
    have heq : (∫ z, dbar ψ z * F z) =
        (∫ z, dbar ψ z * W z) - ∫ z, dbar ψ z * cauchyOperator h z := by
      rw [← integral_sub hiW hiC]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ D
      · simp only [F, indicator_of_mem hz, mul_sub]
      · have hd0 : dbar ψ z = 0 := by
          change dbarLinear (fderiv ℝ ψ z) = 0
          have hnot : z ∉ tsupport (ψ : ℂ → ℂ) := by
            intro hzψ
            apply hz
            have hz1 := (hψV hzψ).2
            exact ball_subset_closedBall ((ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hz1)
          rw [fderiv_of_notMem_tsupport ℝ hnot, map_zero]
        simp only [hd0, zero_mul, sub_self]
    rw [heq, hweak ψ hψ (hψV.trans inter_subset_left),
      cauchyOperator_L1_weak_dbar hh hs ψ (ψ.smooth 1) hψ, sub_self]
  obtain ⟨r, hr, H, hH, hhol, heq⟩ := exists_holomorphic_representative hF hV hFweak hxV
  have hr' : 0 < min r 1 := lt_min hr (by norm_num)
  have hsmall : ball x (min r 1) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r 1, hr', H, hH, hhol.mono hsmall, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall heq,
    ae_restrict_mem measurableSet_ball] with z hz hzball
  have hzD : z ∈ D := ball_subset_closedBall
    ((ball_subset_ball ((min_le_right r 1).trans (by norm_num : (1 : ℝ) ≤ 2))) hzball)
  change D.indicator (fun z => W z - cauchyOperator h z) z = H z at hz
  rw [indicator_of_mem hzD] at hz
  linear_combination hz

end PoincareConjecture.M65Boundary
