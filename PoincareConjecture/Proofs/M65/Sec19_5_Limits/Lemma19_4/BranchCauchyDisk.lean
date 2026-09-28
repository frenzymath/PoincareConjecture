import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyCircle











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric Complex
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]




theorem integral_ball_complex_polar (f : ℂ → E) (R : ℝ) :
    (∫ w in ball (0 : ℂ) R, f w) =
      ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • f (circleMap 0 p.1 p.2) := by
  let T := Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let U := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  have hp (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [circleMap, Complex.exp_mul_I]
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm]
  change (∫ p in U, p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) = _
  have heq : ∀ p ∈ U,
      p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) =
        T.indicator (fun q : ℝ × ℝ => q.1 • f (circleMap 0 q.1 q.2)) p := by
    intro p hpU
    have hp0 : 0 < p.1 := hpU.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [norm_polarCoord_symm, abs_of_pos hp0]
    have hb : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p.1 < R := by
      rw [mem_ball_zero_iff, hn]
    have hT : p ∈ T ↔ p.1 < R :=
      ⟨fun h => h.1.2, fun h => ⟨⟨hp0, h⟩, hpU.2⟩⟩
    by_cases hr : p.1 < R
    · rw [indicator_of_mem (hb.mpr hr), indicator_of_mem (hT.mpr hr), hp]
    · rw [indicator_of_notMem (fun h => hr (hb.mp h)),
        indicator_of_notMem (fun h => hr (hT.mp h)), smul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) heq,
    setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  change (∫ p in U ∩ T, p.1 • f (circleMap 0 p.1 p.2)) =
    ∫ p in T, p.1 • f (circleMap 0 p.1 p.2)
  rw [inter_eq_right.mpr (show T ⊆ U from fun _ hpT => ⟨hpT.1.1, hpT.2⟩)]





theorem integral_inv_smul_dbar_ball [CompleteSpace E] {ψ : ℂ → E}
    (hψ : ContDiff ℝ 1 ψ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun w : ℂ => w⁻¹ • dbar ψ w) (ball (0 : ℂ) R) ∧
      (∫ w in ball (0 : ℂ) R, w⁻¹ • dbar ψ w) =
        (2 : ℂ)⁻¹ • ((∫ θ in (-Real.pi)..Real.pi, ψ (circleMap 0 R θ)) -
          (2 * Real.pi) • ψ 0) := by
  have hi : IntegrableOn (fun w : ℂ => w⁻¹ • dbar ψ w) (closedBall (0 : ℂ) R) :=
    IntegrableOn.smul_continuousOn
      (locallyIntegrable_cauchyKernel.integrableOn_isCompact (isCompact_closedBall _ _))
      (continuous_dbar hψ).continuousOn (isCompact_closedBall _ _)
  refine ⟨hi.mono_set ball_subset_closedBall, ?_⟩
  let T := Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let K := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  let P : ℝ × ℝ → E := fun p =>
    fderiv ℝ ψ (circleMap 0 p.1 p.2) (circleMap 0 1 p.2)
  let Q : ℝ × ℝ → E := fun p =>
    I • fderiv ℝ ψ (circleMap 0 p.1 p.2) (I * circleMap 0 1 p.2)
  have hPC : Continuous P := continuous_cauchyPolarField hψ (continuous_circleMap 0 1)
  have hQC : Continuous Q :=
    (continuous_cauchyPolarField hψ ((continuous_circleMap 0 1).const_mul I)).const_smul I
  have hPI : IntegrableOn P K :=
    hPC.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hQI : IntegrableOn Q K :=
    hQC.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hTK : T ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hrect (H : ℝ × ℝ → E) (hH : IntegrableOn H K) :
      (∫ p in T, H p) = ∫ r in (0 : ℝ)..R, ∫ θ in (-Real.pi)..Real.pi, H (r, θ) := by
    calc
      _ = ∫ p in K, H p :=
        setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)
      _ = ∫ r in Icc (0 : ℝ) R, ∫ θ in Icc (-Real.pi) Real.pi, H (r, θ) :=
        setIntegral_prod H hH
      _ = _ := by
        simp only [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hπ,
          setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  have hPswap : IntegrableOn (Function.uncurry fun r θ : ℝ => P (r, θ))
      (uIoc (0 : ℝ) R ×ˢ uIoc (-Real.pi) Real.pi) := by
    change IntegrableOn P (uIoc (0 : ℝ) R ×ˢ uIoc (-Real.pi) Real.pi)
    rw [uIoc_of_le hR.le, uIoc_of_le hπ]
    exact hPI.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hPint : (∫ p in T, P p) =
      (∫ θ in (-Real.pi)..Real.pi, ψ (circleMap 0 R θ)) - (2 * Real.pi) • ψ 0 := by
    rw [hrect P hPI, intervalIntegral_intervalIntegral_swap hPswap]
    calc
      _ = ∫ θ in (-Real.pi)..Real.pi, ψ (circleMap 0 R θ) - ψ 0 := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact integral_cauchyPolarRadial hψ R θ
      _ = _ := by
        have hc : IntervalIntegrable (fun θ => ψ (circleMap 0 R θ)) volume
            (-Real.pi) Real.pi :=
          (hψ.continuous.comp (continuous_circleMap 0 R)).intervalIntegrable _ _
        rw [intervalIntegral.integral_sub
          hc intervalIntegrable_const, intervalIntegral.integral_const]
        congr 2
        ring
  have hQint : (∫ p in T, Q p) = 0 := by
    rw [hrect Q hQI, intervalIntegral.integral_of_le hR.le]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact integral_cauchyPolarAngular hψ hr.1
  calc
    _ = (2 : ℂ)⁻¹ • ∫ p in T, P p + Q p := by
      rw [integral_ball_complex_polar, ← integral_smul]
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hpT
      exact radial_cauchy_dbar (fderiv ℝ ψ (circleMap 0 p.1 p.2)) hpT.1.1 p.2
    _ = _ := by
      rw [integral_add (hPI.mono_set hTK) (hQI.mono_set hTK), hPint, hQint, add_zero]

end PoincareConjecture.M65Branch
