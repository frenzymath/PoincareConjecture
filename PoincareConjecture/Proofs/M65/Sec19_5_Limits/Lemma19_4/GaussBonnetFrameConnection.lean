import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryFrame

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Gauss

open M65Branch

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem covariantDerivativeAlongMap_smul (D : LeviCivitaData g)
    {H W : ℂ → EuclideanSpace ℝ (Fin n)} {a : ℂ → ℝ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hW : DifferentiableAt ℝ W z) (v : ℂ) :
    covariantDerivativeAlongMap D H (fun w => a w • W w) z v =
      fderiv ℝ a z v • W z + a z • covariantDerivativeAlongMap D H W z v := by
  rw [covariantDerivativeAlongMap, fderiv_fun_smul ha hW]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_smul, covariantDerivativeAlongMap]
  module

theorem normalized_gradient_connection_log (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {z : ℂ}
    (hH : ContDiffAt ℝ ∞ H z)
    (hpos : 0 < g.inner (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1))
    (hconf : ∀ᶠ w in 𝓝 z,
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1) =
        g.inner (H w) (fderiv ℝ H w I) (fderiv ℝ H w I) ∧
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w I) = 0) :
    let lam := fun w => g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1)
    let F := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w))
      (complexGradient H w)
    g.inner (H z) (covariantDerivativeAlongMap D H (fun w => (F w).1) z 1) (F z).2 =
      -fderiv ℝ (fun w => Real.log (lam w)) z I / 2 := by
  let X := fun w => fderiv ℝ H w 1
  let Y := fun w => fderiv ℝ H w I
  let lam := fun w => g.inner (H w) (X w) (X w)
  let a := fun w => (Real.sqrt (lam w))⁻¹
  let F := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w))
    (complexGradient H w)
  have hHd := hH.differentiableAt (by simp)
  have hD := (hH.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hX : DifferentiableAt ℝ X z := hD.clm_apply (differentiableAt_const 1)
  have hY : DifferentiableAt ℝ Y z := hD.clm_apply (differentiableAt_const I)
  have hG : DifferentiableAt ℝ (fun w => g.euclideanCoefficients (H w)) z :=
    ((g.contDiffAt_euclideanCoefficients (H z)).differentiableAt (by simp)).comp z hHd
  have hlam : DifferentiableAt ℝ lam z := (hG.clm_apply hX).clm_apply hX
  have ha : DifferentiableAt ℝ a z := (hlam.sqrt hpos.ne').inv
    (Real.sqrt_pos.mpr hpos).ne'
  have hF1 : (fun w => (F w).1) = fun w => a w • X w := by
    funext w
    simp only [F, normalizedResidualFrame, (residual_columns_complexGradient H w).1,
      (residual_columns_complexGradient H w).2]
    rfl
  have hF2 : (fun w => (F w).2) = fun w => a w • Y w := by
    funext w
    simp only [F, normalizedResidualFrame, (residual_columns_complexGradient H w).1,
      (residual_columns_complexGradient H w).2]
    rfl
  have hcross : g.inner (H z) (X z) (Y z) = 0 := hconf.self_of_nhds.2
  have hzero : (fun w => g.inner (H w) (X w) (Y w)) =ᶠ[𝓝 z] fun _ => 0 :=
    hconf.mono fun _ hw => hw.2
  have hzeroD : fderiv ℝ (fun w => g.inner (H w) (X w) (Y w)) z 1 = 0 := by
    rw [hzero.fderiv_eq, fderiv_const_apply, zero_apply]
  have hmetric := covariantDerivativeAlongMap_metricCompatible D hHd hX hY 1
  rw [hzeroD] at hmetric
  have hnorm := covariantDerivativeAlongMap_metricCompatible D hHd hX hX I
  change fderiv ℝ lam z I = _ at hnorm
  rw [g.symm (H z) (X z)] at hnorm
  have htorsion : covariantDerivativeAlongMap D H Y z 1 =
      covariantDerivativeAlongMap D H X z I := by
    change covariantDerivativeAlongMap D H (fun w => fderiv ℝ H w I) z 1 =
      covariantDerivativeAlongMap D H (fun w => fderiv ℝ H w 1) z I
    rw [covariantDerivativeAlongMap_fderiv_const D hH,
      covariantDerivativeAlongMap_fderiv_const D hH, covariantHessianMap_symm D hH]
  rw [htorsion, g.symm (H z) (X z)] at hmetric
  have hpair : g.inner (H z) (covariantDerivativeAlongMap D H X z 1) (Y z) =
      -fderiv ℝ lam z I / 2 := by linarith only [hmetric, hnorm]
  have hscale : a z * a z = (lam z)⁻¹ := by
    dsimp only [a]
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  change g.inner (H z) (covariantDerivativeAlongMap D H (fun w => (F w).1) z 1)
    (F z).2 = -fderiv ℝ (fun w => Real.log (lam w)) z I / 2
  rw [hF1, congrFun hF2 z, covariantDerivativeAlongMap_smul D ha hX]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, hcross,
    mul_zero, zero_add, hpair, fderiv.log hlam hpos.ne']
  calc
    _ = (a z * a z) * (-fderiv ℝ lam z I / 2) := by ring
    _ = _ := by rw [hscale]; ring

theorem rotated_frame_connection (D : LeviCivitaData g)
    {H T N : ℂ → EuclideanSpace ℝ (Fin n)} {a b : ℂ → ℝ} {z : ℂ}
    (hH : DifferentiableAt ℝ H z) (hT : DifferentiableAt ℝ T z)
    (hN : DifferentiableAt ℝ N z)
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z)
    (horth : ∀ᶠ w in 𝓝 z, g.inner (H w) (T w) (T w) = 1 ∧
      g.inner (H w) (T w) (N w) = 0 ∧ g.inner (H w) (N w) (N w) = 1)
    (hab : a z ^ 2 + b z ^ 2 = 1) (v : ℂ) :
    g.inner (H z)
        (covariantDerivativeAlongMap D H (fun w => a w • T w + b w • N w) z v)
        ((-b z) • T z + a z • N z) =
      g.inner (H z) (covariantDerivativeAlongMap D H T z v) (N z) +
        a z * fderiv ℝ b z v - b z * fderiv ℝ a z v := by
  have heTT : (fun w => g.inner (H w) (T w) (T w)) =ᶠ[𝓝 z] fun _ => 1 :=
    horth.mono fun _ h => h.1
  have heNN : (fun w => g.inner (H w) (N w) (N w)) =ᶠ[𝓝 z] fun _ => 1 :=
    horth.mono fun _ h => h.2.2
  have heTN : (fun w => g.inner (H w) (T w) (N w)) =ᶠ[𝓝 z] fun _ => 0 :=
    horth.mono fun _ h => h.2.1
  have hTT := covariantDerivativeAlongMap_metricCompatible D hH hT hT v
  rw [heTT.fderiv_eq, fderiv_const_apply, zero_apply, g.symm (H z) (T z)] at hTT
  have hNN := covariantDerivativeAlongMap_metricCompatible D hH hN hN v
  rw [heNN.fderiv_eq, fderiv_const_apply, zero_apply, g.symm (H z) (N z)] at hNN
  have hTN := covariantDerivativeAlongMap_metricCompatible D hH hT hN v
  rw [heTN.fderiv_eq, fderiv_const_apply, zero_apply, g.symm (H z) (T z)] at hTN
  have hdt : g.inner (H z) (covariantDerivativeAlongMap D H T z v) (T z) = 0 := by
    linarith only [hTT]
  have hdn : g.inner (H z) (covariantDerivativeAlongMap D H N z v) (N z) = 0 := by
    linarith only [hNN]
  have hswap : g.inner (H z) (covariantDerivativeAlongMap D H N z v) (T z) =
      -g.inner (H z) (covariantDerivativeAlongMap D H T z v) (N z) := by
    linarith only [hTN]
  have hrot : covariantDerivativeAlongMap D H (fun w => a w • T w + b w • N w) z v =
      fderiv ℝ a z v • T z + a z • covariantDerivativeAlongMap D H T z v +
        (fderiv ℝ b z v • N z + b z • covariantDerivativeAlongMap D H N z v) := by
    have hadd := ((ha.hasFDerivAt.smul hT.hasFDerivAt).add
      (hb.hasFDerivAt.smul hN.hasFDerivAt)).fderiv
    change fderiv ℝ (fun w => a w • T w + b w • N w) z = _ at hadd
    rw [covariantDerivativeAlongMap, hadd]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, covariantDerivativeAlongMap]
    module
  obtain ⟨hTnorm, hcross, hNnorm⟩ := horth.self_of_nhds
  have hcross' : g.inner (H z) (N z) (T z) = 0 := (g.symm _ _ _).trans hcross
  rw [hrot]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    hTnorm, hcross, hcross', hNnorm, hdt, hdn, hswap]
  calc
    _ = (a z ^ 2 + b z ^ 2) *
        g.inner (H z) (covariantDerivativeAlongMap D H T z v) (N z) +
          a z * fderiv ℝ b z v - b z * fderiv ℝ a z v := by ring
    _ = _ := by rw [hab, one_mul]

theorem normalizedResidualFrame_smul
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v) (q : Fin n → ℂ) (s : ℂ)
    (hcross : G (residualRealColumn q) (residualImagColumn q) = 0)
    (hdiag : G (residualImagColumn q) (residualImagColumn q) =
      G (residualRealColumn q) (residualRealColumn q)) :
    let F := normalizedResidualFrame G q
    (normalizedResidualFrame G (s • q)).1 =
        (s.re / ‖s‖) • F.1 + (s.im / ‖s‖) • F.2 ∧
      (normalizedResidualFrame G (s • q)).2 =
        (-s.im / ‖s‖) • F.1 + (s.re / ‖s‖) • F.2 := by
  let a := residualRealColumn q
  let b := residualImagColumn q
  let rho := G a a
  obtain ⟨hsa, hsb⟩ := residual_columns_smul s q
  have hba : G b a = 0 := (hG _ _).trans hcross
  have hscale : G (residualRealColumn (s • q)) (residualRealColumn (s • q)) =
      ‖s‖ ^ 2 * rho := by
    rw [hsa]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
      hcross, hba, hdiag, rho, a, b, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsqrt : Real.sqrt (G (residualRealColumn (s • q)) (residualRealColumn (s • q))) =
      ‖s‖ * Real.sqrt rho := by
    rw [hscale, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  dsimp only [normalizedResidualFrame]
  rw [hsqrt, hsa, hsb]
  simp only [mul_inv_rev, smul_add, smul_smul, div_eq_mul_inv, a, rho]
  constructor <;> module

theorem complex_phase_connection_term {s : ℂ → ℂ} {z : ℂ}
    (hs : DifferentiableAt ℝ s z) (hne : s z ≠ 0) (v : ℂ) :
    (s z).re / ‖s z‖ * fderiv ℝ (fun w => (s w).im / ‖s w‖) z v -
      (s z).im / ‖s z‖ * fderiv ℝ (fun w => (s w).re / ‖s w‖) z v =
        (fderiv ℝ s z v / s z).im := by
  let d := fun w => ‖s w‖⁻¹
  have hn : ‖s z‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hd : DifferentiableAt ℝ d z := (hs.norm ℝ hne).inv hn
  have hr := Complex.reCLM.hasFDerivAt.comp z hs.hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z hs.hasFDerivAt
  have hreal : fderiv ℝ (fun w => (s w).re / ‖s w‖) z v =
      (fderiv ℝ s z v).re * d z + (s z).re * fderiv ℝ d z v := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hr.mul hd.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => (s w).re * d w) z v = _ at h
    change fderiv ℝ (fun w => (s w).re * d w) z v = _
    rw [h]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, Complex.reCLM_apply, Function.comp_def]
    ring
  have himag : fderiv ℝ (fun w => (s w).im / ‖s w‖) z v =
      (fderiv ℝ s z v).im * d z + (s z).im * fderiv ℝ d z v := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hi.mul hd.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => (s w).im * d w) z v = _ at h
    change fderiv ℝ (fun w => (s w).im * d w) z v = _
    rw [h]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, Complex.imCLM_apply, Function.comp_def]
    ring
  rw [hreal, himag, Complex.div_im, Complex.normSq_eq_norm_sq]
  dsimp only [d]
  field_simp
  ring

theorem complex_power_connection_nonpos (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    (fderiv ℝ (fun w : ℂ => w ^ m) z 1 / z ^ m).im =
        (m : ℝ) * z⁻¹.im ∧
      (fderiv ℝ (fun w : ℂ => w ^ m) z 1 / z ^ m).im ≤ 0 := by
  have hzne : z ≠ 0 := by
    intro h
    simp only [h, zero_im, lt_self_iff_false] at hz
  have hder : fderiv ℝ (fun w : ℂ => w ^ m) z 1 = (m : ℂ) * z ^ (m - 1) := by
    have h := ((hasDerivAt_id z).pow m).hasFDerivAt.restrictScalars ℝ
    have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h.fderiv
    change fderiv ℝ (fun w : ℂ => w ^ m) z 1 =
      (1 : ℂ) * ((m : ℂ) * z ^ (m - 1) * 1) at hh
    simpa only [one_mul, mul_one] using hh
  have heq : fderiv ℝ (fun w : ℂ => w ^ m) z 1 / z ^ m = (m : ℂ) * z⁻¹ := by
    rw [hder]
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_sub_one, pow_succ]
      field_simp
  have him : ((m : ℂ) * z⁻¹).im = (m : ℝ) * z⁻¹.im := by simp
  rw [heq, him]
  refine ⟨rfl, mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_⟩
  rw [Complex.inv_im]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.le) (Complex.normSq_nonneg z)

theorem residual_frame_connection_log (D : LeviCivitaData g) (m : ℕ)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ} {z : ℂ}
    (hz : 0 < z.im) (hH : ContDiffAt ℝ ∞ H z)
    (hQ : DifferentiableAt ℝ Q z) (hQne : Q z ≠ 0)
    (hfactor : ∀ᶠ w in 𝓝 z, complexGradient H w = w ^ m • Q w)
    (hconf : ∀ᶠ w in 𝓝 z,
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1) =
        g.inner (H w) (fderiv ℝ H w I) (fderiv ℝ H w I) ∧
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w I) = 0) :
    let lam := fun w => g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1)
    let F := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w)) (Q w)
    let A := g.inner (H z)
      (covariantDerivativeAlongMap D H (fun w => (F w).1) z 1) (F z).2;
    -fderiv ℝ (fun w => Real.log (lam w)) z I / 2 = A + (m : ℝ) * z⁻¹.im ∧
      -fderiv ℝ (fun w => Real.log (lam w)) z I / 2 ≤ A := by
  let G := fun w => g.euclideanCoefficients (H w)
  let X := fun w => residualRealColumn (Q w)
  let Y := fun w => residualImagColumn (Q w)
  let rho := fun w => G w (X w) (X w)
  let F := fun w => normalizedResidualFrame (G w) (Q w)
  let J := fun w => normalizedResidualFrame (G w) (complexGradient H w)
  let s := fun w : ℂ => w ^ m
  let a := fun w => (s w).re / ‖s w‖
  let b := fun w => (s w).im / ‖s w‖
  have hzne : z ≠ 0 := by
    intro h
    simp only [h, zero_im, lt_self_iff_false] at hz
  have hsne : s z ≠ 0 := pow_ne_zero m hzne
  have hs : DifferentiableAt ℝ s z := differentiableAt_id.pow m
  have hsn : ‖s z‖ ≠ 0 := norm_ne_zero_iff.mpr hsne
  have hsre : DifferentiableAt ℝ (fun w => (s w).re) z :=
    (Complex.reCLM.hasFDerivAt.comp z hs.hasFDerivAt).differentiableAt
  have hsim : DifferentiableAt ℝ (fun w => (s w).im) z :=
    (Complex.imCLM.hasFDerivAt.comp z hs.hasFDerivAt).differentiableAt
  have ha : DifferentiableAt ℝ a z := by
    simpa +instances only [a, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using!
      hsre.mul ((hs.norm ℝ hsne).inv hsn)
  have hb : DifferentiableAt ℝ b z := by
    simpa +instances only [b, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using!
      hsim.mul ((hs.norm ℝ hsne).inv hsn)
  have hres : ∀ᶠ w in 𝓝 z, G w (X w) (Y w) = 0 ∧
      G w (Y w) (Y w) = G w (X w) (X w) := by
    filter_upwards [hfactor, hconf, eventually_ne_nhds hzne] with w hf hc hn
    obtain ⟨he1, heI⟩ := residual_columns_complexGradient H w
    rw [hf] at he1 heI
    exact residual_columns_conformal_of_smul (G w) (g.symm (H w))
      (pow_ne_zero m hn) (Q w) (by simpa +instances only [G, he1, heI] using! hc.2)
      (by simpa +instances only [G, he1, heI] using! hc.1.symm)
  have hpos : 0 < rho z := residual_columns_factor_pos (G z) (g.pos (H z))
    hQne hres.self_of_nhds.2
  have hHd := hH.differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G z :=
    ((g.contDiffAt_euclideanCoefficients (H z)).differentiableAt (by simp)).comp z hHd
  have hX : DifferentiableAt ℝ X z := residualRealColumn.differentiableAt.comp z hQ
  have hY : DifferentiableAt ℝ Y z := residualImagColumn.differentiableAt.comp z hQ
  have hrho : DifferentiableAt ℝ rho z := (hG.clm_apply hX).clm_apply hX
  have hscale : DifferentiableAt ℝ (fun w => (Real.sqrt (rho w))⁻¹) z :=
    (hrho.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
  have hT : DifferentiableAt ℝ (fun w => (F w).1) z := hscale.smul hX
  have hN : DifferentiableAt ℝ (fun w => (F w).2) z := hscale.smul hY
  have horth : ∀ᶠ w in 𝓝 z, g.inner (H w) (F w).1 (F w).1 = 1 ∧
      g.inner (H w) (F w).1 (F w).2 = 0 ∧ g.inner (H w) (F w).2 (F w).2 = 1 := by
    filter_upwards [hres, hQ.continuousAt.eventually_ne hQne] with w hc hn
    exact normalizedResidualFrame_orthonormal (G w) (Q w)
      (residual_columns_factor_pos (G w) (g.pos (H w)) hn hc.2) hc.1 hc.2
  have hab : a z ^ 2 + b z ^ 2 = 1 := by
    dsimp only [a, b]
    rw [div_pow, div_pow, ← add_div]
    have hn : (s z).re ^ 2 + (s z).im ^ 2 = ‖s z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hn, div_self (pow_ne_zero 2 hsn)]
  have hrotation : ∀ᶠ w in 𝓝 z,
      (J w).1 = a w • (F w).1 + b w • (F w).2 ∧
        (J w).2 = (-b w) • (F w).1 + a w • (F w).2 := by
    filter_upwards [hfactor, hres] with w hf hc
    dsimp only [J]
    rw [hf]
    simpa only [F, a, b, s, neg_div] using
      normalizedResidualFrame_smul (G w) (g.symm (H w)) (Q w) (w ^ m) hc.1 hc.2
  have hfirst : (fun w => (J w).1) =ᶠ[𝓝 z]
      (fun w => a w • (F w).1 + b w • (F w).2) := hrotation.mono fun _ h => h.1
  have hconn : covariantDerivativeAlongMap D H (fun w => (J w).1) z 1 =
      covariantDerivativeAlongMap D H
        (fun w => a w • (F w).1 + b w • (F w).2) z 1 := by
    simp only [covariantDerivativeAlongMap, hfirst.fderiv_eq, hfirst.self_of_nhds]
  have hrot := rotated_frame_connection D hHd hT hN ha hb horth hab 1
  rw [← hconn, ← hrotation.self_of_nhds.2] at hrot
  have hgradne : complexGradient H z ≠ 0 := by
    rw [hfactor.self_of_nhds]
    exact smul_ne_zero hsne hQne
  have hposH : 0 < g.inner (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1) := by
    have hh := residual_columns_factor_pos (G z) (g.pos (H z)) hgradne
      (by simpa +instances only [G, (residual_columns_complexGradient H z).1,
        (residual_columns_complexGradient H z).2] using! hconf.self_of_nhds.1.symm)
    simpa +instances only [G, (residual_columns_complexGradient H z).1] using! hh
  have hlog := normalized_gradient_connection_log D hH hposH hconf
  have hphase := complex_phase_connection_term hs hsne 1
  have hpower := complex_power_connection_nonpos m hz
  change g.inner (H z) (covariantDerivativeAlongMap D H (fun w => (J w).1) z 1)
    (J z).2 = _ at hlog
  change a z * fderiv ℝ b z 1 - b z * fderiv ℝ a z 1 = _ at hphase
  dsimp only
  constructor
  · linarith only [hlog, hrot, hphase, hpower.1]
  · linarith only [hlog, hrot, hphase, hpower.2]

end PoincareConjecture.M65Gauss
