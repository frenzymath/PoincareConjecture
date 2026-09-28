import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressWeakModes












set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) 1)





theorem m64AnnulusStress_trigonometric_modes_zero
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {c : ℝ} (hc : 0 ≤ c)
    (hfirst : ∀ eta rho : ℝ → ℝ, ContDiff ℝ ∞ eta →
      Function.Periodic eta curvePeriod → ContDiff ℝ ∞ rho → HasCompactSupport rho →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p) = 0)
    (hsecond : ∀ eta rho : ℝ → ℝ, ContDiff ℝ ∞ eta →
      Function.Periodic eta curvePeriod → ContDiff ℝ ∞ rho → HasCompactSupport rho →
      tsupport rho ⊆ Ioo (0 : ℝ) 1 →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * (-c * V p) +
        eta (p 0) * deriv rho (p 1) * U p) = 0)
    (j : ℤ) :
    m64HorizontalMoment (fun x => Real.cos (j * x)) V =ᵐ[nu] (fun _ => 0) ∧
    m64HorizontalMoment (fun x => Real.sin (j * x)) V =ᵐ[nu] (fun _ => 0) ∧
    (j ≠ 0 →
      m64HorizontalMoment (fun x => Real.cos (j * x)) U =ᵐ[nu] (fun _ => 0) ∧
      m64HorizontalMoment (fun x => Real.sin (j * x)) U =ᵐ[nu] (fun _ => 0)) := by
  have hcos : ContDiff ℝ ∞ (fun x : ℝ => Real.cos (j * x)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have hsin : ContDiff ℝ ∞ (fun x : ℝ => Real.sin (j * x)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hcper : Function.Periodic (fun x : ℝ => Real.cos (j * x)) curvePeriod := by
    intro x
    change Real.cos (j * (x + 2 * Real.pi)) = Real.cos (j * x)
    rw [mul_add, Real.cos_add_int_mul_two_pi]
  have hsper : Function.Periodic (fun x : ℝ => Real.sin (j * x)) curvePeriod := by
    intro x
    change Real.sin (j * (x + 2 * Real.pi)) = Real.sin (j * x)
    rw [mul_add, Real.sin_add_int_mul_two_pi]
  have hcos' (x : ℝ) : deriv (fun x : ℝ => Real.cos (j * x)) x =
      -(j : ℝ) * Real.sin (j * x) := by
    simpa only [id_eq, mul_one, neg_mul, mul_neg, mul_comm] using
      (((hasDerivAt_id x).const_mul (j : ℝ)).cos).deriv
  have hsin' (x : ℝ) : deriv (fun x : ℝ => Real.sin (j * x)) x =
      (j : ℝ) * Real.cos (j * x) := by
    simpa only [id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id x).const_mul (j : ℝ)).sin).deriv
  have hcm := m64AnnulusStress_angular_mode_zero hU hV hc hcos hsin hcos'
    (by simpa only [neg_neg] using hsin')
    (fun rho hr hs => hfirst _ rho hcos hcper hr hs)
    (fun rho hr hs ht => hsecond _ rho hsin hsper hr hs ht)
  have hsm := m64AnnulusStress_angular_mode_zero hU hV hc hsin hcos hsin' hcos'
    (fun rho hr hs => hfirst _ rho hsin hsper hr hs)
    (fun rho hr hs ht => hsecond _ rho hcos hcper hr hs ht)
  refine ⟨hcm.1, hsm.1, fun hj => ?_⟩
  have hjr : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  constructor
  · filter_upwards [hsm.2] with s hs
    exact (mul_eq_zero.mp hs).resolve_left hjr
  · filter_upwards [hcm.2] with s hs
    exact (mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr hjr)





theorem m64AnnulusStress_constant_mode_zero
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu) {c : ℝ}
    (hsecond : ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → HasCompactSupport rho →
      tsupport rho ⊆ Ioo (0 : ℝ) 1 →
      (∫ p in S, deriv (fun _ : ℝ => (1 : ℝ)) (p 0) * rho (p 1) * (-c * V p) +
        (1 : ℝ) * deriv rho (p 1) * U p) = 0)
    (hbalance : (∫ p in S, U p) = 0) :
    m64HorizontalMoment (fun _ => 1) U =ᵐ[nu] (fun _ => 0) := by
  have hi := m64HorizontalMoment_integrable (theta := fun _ => 1) continuous_const hU
  obtain ⟨b, hb⟩ := M08.weak_derivative_zero_ae_const (by norm_num : (0 : ℝ) < 1)
    (m64HorizontalMoment (fun _ => 1) U)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hi)
    (by
      intro rho hr hs ht
      have h := m64LocalizedStress_moment_weak (hV.const_mul (-c)) hU contDiff_const hr
        (hsecond rho hr hs ht)
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc, smul_eq_mul, deriv_const, m64HorizontalMoment,
        zero_mul, integral_zero, mul_zero, neg_zero] using h)
  have hmean : (∫ s in Icc (0 : ℝ) 1, m64HorizontalMoment (fun _ => 1) U s) = 0 := by
    have h := m64HorizontalMoment_pairing (theta := fun _ => 1) (rho := fun _ => 1)
      continuous_const continuous_const hU
    simpa only [one_mul, hbalance] using h
  have hb0 : b = 0 := by
    rw [integral_congr_ae hb] at hmean
    simpa using hmean
  filter_upwards [hb] with s hs
  exact hs.trans hb0

end PoincareConjecture
