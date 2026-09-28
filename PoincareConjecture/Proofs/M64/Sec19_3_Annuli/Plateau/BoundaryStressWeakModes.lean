import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressMoments
import PoincareConjecture.Proofs.M64.Mathlib.WeakDirichletMode













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




theorem m64LocalizedStress_moment_weak
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta) (hrho : ContDiff ℝ ∞ rho)
    (hstress : (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
      eta (p 0) * deriv rho (p 1) * V p) = 0) :
    (∫ s in Icc (0 : ℝ) 1, deriv rho s * m64HorizontalMoment eta V s) =
      -(∫ s in Icc (0 : ℝ) 1, rho s * m64HorizontalMoment (deriv eta) U s) := by
  have hcU : Continuous (fun p : LoopPlane => deriv eta (p 0) * rho (p 1)) :=
    ((heta.continuous_deriv (by simp)).comp (EuclideanSpace.proj 0).continuous).mul
      (hrho.continuous.comp (EuclideanSpace.proj 1).continuous)
  have hcV : Continuous (fun p : LoopPlane => eta (p 0) * deriv rho (p 1)) :=
    (heta.continuous.comp (EuclideanSpace.proj 0).continuous).mul
      ((hrho.continuous_deriv (by simp)).comp (EuclideanSpace.proj 1).continuous)
  rw [integral_add (m64Annulus_continuous_mul_integrable hU hcU)
    (m64Annulus_continuous_mul_integrable hV hcV)] at hstress
  rw [m64HorizontalMoment_pairing heta.continuous (hrho.continuous_deriv (by simp)) hV,
    m64HorizontalMoment_pairing (heta.continuous_deriv (by simp)) hrho.continuous hU]
  linarith





theorem m64AnnulusStress_angular_mode_zero
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {c alpha : ℝ} (hc : 0 ≤ c) {eta theta : ℝ → ℝ}
    (heta : ContDiff ℝ ∞ eta) (htheta : ContDiff ℝ ∞ theta)
    (heta' : ∀ x, deriv eta x = alpha * theta x)
    (htheta' : ∀ x, deriv theta x = -alpha * eta x)
    (hfirst : ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → HasCompactSupport rho →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p) = 0)
    (hsecond : ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho → HasCompactSupport rho →
      tsupport rho ⊆ Ioo (0 : ℝ) 1 →
      (∫ p in S, deriv theta (p 0) * rho (p 1) * (-c * V p) +
        theta (p 0) * deriv rho (p 1) * U p) = 0) :
    m64HorizontalMoment eta V =ᵐ[nu] (fun _ => 0) ∧
      (fun s => alpha * m64HorizontalMoment theta U s) =ᵐ[nu] (fun _ => 0) := by
  obtain ⟨hcont, heq, hboundary⟩ := m64LocalizedStress_zero_boundary_moment hU hV heta hfirst
  have hsign : 0 ≤ alpha * (c * alpha) := by
    calc
      _ = c * alpha ^ 2 := by ring
      _ ≥ 0 := mul_nonneg hc (sq_nonneg alpha)
  apply m64WeakDirichlet_coupled_zero (alpha := alpha) (beta := c * alpha)
    (by norm_num : (0 : ℝ) < 1) hsign
    (m64HorizontalMoment_integrable htheta.continuous hU)
    hcont heq (by simp only [intervalIntegral.integral_same]) hboundary
  · intro rho hrho hcompact _
    have h := m64LocalizedStress_moment_weak hU hV heta hrho (hfirst rho hrho hcompact)
    have hmoment (s : ℝ) : m64HorizontalMoment (deriv eta) U s =
        alpha * m64HorizontalMoment theta U s := by
      dsimp only [m64HorizontalMoment]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change deriv eta x * U (annulusPoint x s) = _
        rw [heta']
        ring
    simpa only [hmoment] using h
  · intro rho hrho hcompact hs
    have h := m64LocalizedStress_moment_weak (hV.const_mul (-c)) hU htheta hrho
      (hsecond rho hrho hcompact hs)
    have hmoment (s : ℝ) : m64HorizontalMoment (deriv theta) (fun p => -c * V p) s =
        (c * alpha) * m64HorizontalMoment eta V s := by
      dsimp only [m64HorizontalMoment]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change deriv theta x * (-c * V (annulusPoint x s)) = _
        rw [htheta']
        ring
    simpa only [hmoment] using h

end PoincareConjecture
