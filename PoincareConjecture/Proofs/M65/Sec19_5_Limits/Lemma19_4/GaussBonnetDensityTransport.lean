import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetLaplacian
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex InnerProductSpace
open scoped Topology ContDiff Laplacian

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace

private theorem dbar_gradient_laplacian {n : ℕ}
    {G : ℂ → EuclideanSpace ℝ (Fin n)} {z : ℂ}
    (hG : ContDiffAt ℝ ∞ G z) :
    dbar (complexGradient G) z =
      (2 : ℂ)⁻¹ • coordinateComplexification (Δ G z) := by
  simpa only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    using dbar_complexGradient hG

private theorem laplacian_vector_comp_holomorphic {n : ℕ}
    {G : ℂ → EuclideanSpace ℝ (Fin n)} {psi : ℂ → ℂ} {z : ℂ}
    (hG : ContDiffAt ℝ ∞ G (psi z)) (hpsi : ContDiffAt ℂ ∞ psi z) :
    Δ (G ∘ psi) z = ‖deriv psi z‖ ^ 2 • Δ G (psi z) := by
  have hGR : ContDiffAt ℝ ∞ (G ∘ psi) z := hG.comp z (hpsi.restrict_scalars ℝ)
  have hgd : DifferentiableAt ℝ (complexGradient G) (psi z) := by
    have hD : ContDiffAt ℝ 1 (fderiv ℝ G) (psi z) :=
      hG.fderiv_right (WithTop.coe_le_coe.mpr le_top)
    exact ((coordinateComplexification.contDiff.contDiffAt.comp _
      (hD.clm_apply contDiffAt_const)).sub
        ((coordinateComplexification.contDiff.contDiffAt.comp _
          (hD.clm_apply contDiffAt_const)).const_smul I)).differentiableAt one_ne_zero
  have hpd : DifferentiableAt ℂ (deriv psi) z := by
    have hh : ContDiffAt ℂ 1 (fun w => fderiv ℂ psi w 1) z :=
      (hpsi.fderiv_right (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
    simpa only [fderiv_apply_one_eq_deriv] using hh.differentiableAt one_ne_zero
  have hpsiD := (hpsi.differentiableAt (by simp)).hasDerivAt
  have hnearG : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ G (psi w) :=
    hpsi.continuousAt.eventually (((hG.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually
      (by simp)).mono (fun _ hw => hw.differentiableAt one_ne_zero))
  have hnearP : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ psi w :=
    ((hpsi.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hw => hw.differentiableAt one_ne_zero)
  have hfield : complexGradient (G ∘ psi) =ᶠ[𝓝 z]
      fun w => deriv psi w • complexGradient G (psi w) := by
    filter_upwards [hnearG, hnearP] with w hw hp
    exact complexGradient_comp_holomorphic hw hp.hasDerivAt
  have hbar : dbar (complexGradient (G ∘ psi)) z =
      dbar (fun w => deriv psi w • complexGradient G (psi w)) z :=
    congrArg dbarLinear hfield.fderiv_eq
  change dbar (complexGradient (G ∘ psi)) z =
    dbar (fun w => deriv psi w • (complexGradient G ∘ psi) w) z at hbar
  rw [dbar_smul (hpd.restrictScalars ℝ)
      (hgd.comp z (hpsiD.differentiableAt.restrictScalars ℝ)),
    dbar_eq_zero_of_differentiableAt_complex hpd, zero_smul, zero_add,
    dbar_comp_holomorphic hgd hpsiD,
    dbar_gradient_laplacian hGR, dbar_gradient_laplacian hG] at hbar
  have hs : deriv psi z * star (deriv psi z) = (‖deriv psi z‖ ^ 2 : ℝ) := by
    change deriv psi z * (starRingEnd ℂ) (deriv psi z) = (‖deriv psi z‖ ^ 2 : ℝ)
    simpa only [ofReal_pow] using Complex.mul_conj' (deriv psi z)
  rw [smul_smul, hs] at hbar
  have hh := congrArg (fun q : Fin n → ℂ => (2 : ℂ) • q) hbar
  simp only [smul_smul] at hh
  have htwo : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
  have hreorder : (2 : ℂ) * ((‖deriv psi z‖ ^ 2 : ℝ) * (2 : ℂ)⁻¹) =
      (‖deriv psi z‖ ^ 2 : ℝ) := by
    rw [mul_left_comm, htwo, mul_one]
  rw [htwo, one_smul, hreorder] at hh
  ext i
  have hi := congrArg (fun q : Fin n → ℂ => (q i).re) hh
  change (((Δ (G ∘ psi) z) i : ℝ) : ℂ).re =
    (((‖deriv psi z‖ ^ 2 : ℝ) : ℂ) * (((Δ G (psi z)) i : ℝ) : ℂ)).re at hi
  simpa only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    PiLp.smul_apply, smul_eq_mul] using hi

theorem laplacian_comp_holomorphic {f : ℂ → ℝ} {psi : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f (psi z)) (hpsi : ContDiffAt ℂ ∞ psi z) :
    Δ (f ∘ psi) z = ‖deriv psi z‖ ^ 2 * Δ f (psi z) := by
  let v := EuclideanSpace.basisFun (Fin 1) ℝ 0
  let J : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hJ : ContDiffAt ℝ ∞ (J ∘ f) (psi z) := J.contDiff.contDiffAt.comp _ hf
  have hh := laplacian_vector_comp_holomorphic hJ hpsi
  change Δ (J ∘ (f ∘ psi)) z = ‖deriv psi z‖ ^ 2 • Δ (J ∘ f) (psi z) at hh
  rw [((hf.comp z (hpsi.restrict_scalars ℝ)).of_le
      (WithTop.coe_le_coe.mpr le_top)).laplacian_CLM_comp_left,
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).laplacian_CLM_comp_left] at hh
  have hi := congrArg (fun w : EuclideanSpace ℝ (Fin 1) => w 0) hh
  simpa only [Function.comp_apply, J, v, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_true, mul_one] using hi

theorem logarithmic_laplacian_comp_holomorphic
    {lambda localFactor : ℂ → ℝ} {psi : ℂ → ℂ} {z : ℂ}
    (hlambda : ContDiffAt ℝ ∞ lambda (psi z)) (hpos : 0 < lambda (psi z))
    (hpsi : AnalyticAt ℂ psi z) (hne : deriv psi z ≠ 0)
    (heq : localFactor =ᶠ[𝓝 z] fun w => lambda (psi w) * ‖deriv psi w‖ ^ 2) :
    Δ (fun w => Real.log (localFactor w)) z =
      ‖deriv psi z‖ ^ 2 * Δ (fun w => Real.log (lambda w)) (psi z) := by
  have hlog : ContDiffAt ℝ ∞ (fun w => Real.log (lambda w)) (psi z) :=
    hlambda.log hpos.ne'
  have hharm : HarmonicAt (fun w => Real.log ‖deriv psi w‖) z :=
    hpsi.deriv.harmonicAt_log_norm hne
  have hnearL : ∀ᶠ w in 𝓝 z, lambda (psi w) ≠ 0 :=
    (hlambda.continuousAt.comp hpsi.continuousAt).eventually_ne hpos.ne'
  have hnearD : ∀ᶠ w in 𝓝 z, deriv psi w ≠ 0 :=
    hpsi.deriv.continuousAt.eventually_ne hne
  have hlogs : (fun w => Real.log (localFactor w)) =ᶠ[𝓝 z]
      fun w => Real.log (lambda (psi w)) + 2 * Real.log ‖deriv psi w‖ := by
    filter_upwards [heq, hnearL, hnearD] with w hw hL hD
    rw [hw, Real.log_mul hL (pow_ne_zero 2 (norm_ne_zero_iff.mpr hD)), Real.log_pow]
    norm_num
  have hsum := ((hlog.comp z (hpsi.contDiffAt.restrict_scalars ℝ)).of_le
    (WithTop.coe_le_coe.mpr le_top)).laplacian_add (hharm.1.const_smul (2 : ℝ))
  change Δ (fun w => Real.log (lambda (psi w)) + 2 * Real.log ‖deriv psi w‖) z =
    Δ ((fun w => Real.log (lambda w)) ∘ psi) z +
      Δ (fun w => 2 * Real.log ‖deriv psi w‖) z at hsum
  have hmul := laplacian_smul (2 : ℝ) hharm.1
  change Δ (fun w => 2 * Real.log ‖deriv psi w‖) z =
    2 * Δ (fun w => Real.log ‖deriv psi w‖) z at hmul
  rw [(laplacian_congr_nhds hlogs).self_of_nhds, hsum, hmul,
    hharm.2.self_of_nhds, Pi.zero_apply, mul_zero, add_zero]
  exact laplacian_comp_holomorphic hlog hpsi.contDiffAt

theorem det_real_fderiv_holomorphic {psi : ℂ → ℂ} {z p : ℂ}
    (hpsi : HasDerivAt psi p z) : (fderiv ℝ psi z).det = ‖p‖ ^ 2 := by
  have hd := hpsi.hasFDerivAt.restrictScalars ℝ
  have hcol (v : ℂ) : fderiv ℝ psi z v = v * p := by
    simpa only [ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      congrArg (fun D : ℂ →L[ℝ] ℂ => D v) hd.fderiv
  change LinearMap.det (fderiv ℝ psi z).toLinearMap = _
  rw [← LinearMap.det_toMatrix orthonormalBasisOneI.toBasis, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, orthonormalBasisOneI_repr_apply,
    coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change (fderiv ℝ psi z 1).re * (fderiv ℝ psi z I).im -
    (fderiv ℝ psi z I).re * (fderiv ℝ psi z 1).im = _
  rw [hcol, hcol, one_mul, I_mul_re, I_mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end PoincareConjecture.M65Gauss
