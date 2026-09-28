import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicChangeOfVariables
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

set_option autoImplicit false

open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
  {t : ℝ} {sigma : ℝ → ℝ}

theorem integral_density_comp_monotone
    (hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t))
    (hsigma : ContDiff ℝ 1 sigma) (hmono : Monotone sigma)
    (A : ℝ → ℝ) (hA : Continuous (fun y => A y * curveSpeed F c t y))
    (alpha beta : ℝ) :
    (∫ x in alpha..beta,
      A (sigma x) * curveSpeed F (fun y s => c (sigma y) s) t x) =
      ∫ y in sigma alpha..sigma beta, A y * curveSpeed F c t y := by
  calc
    _ = ∫ x in alpha..beta,
        (A (sigma x) * curveSpeed F c t (sigma x)) * deriv sigma x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only
      rw [M63.curveSpeed_comp F c (hc (sigma x))
        (hsigma.differentiable (by norm_num) x).hasDerivAt hmono.deriv_nonneg]
      ring
    _ = _ := intervalIntegral.integral_comp_mul_deriv
      (fun x _hx => (hsigma.differentiable (by norm_num) x).hasDerivAt)
      hsigma.continuous_deriv_one.continuousOn hA

theorem arcLength_comp_monotone
    (hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t))
    (hv : Continuous (curveSpeed F c t))
    (hsigma : ContDiff ℝ 1 sigma) (hmono : Monotone sigma)
    (alpha beta : ℝ) :
    m63ArcLength F (fun y s => c (sigma y) s) t alpha beta =
      m63ArcLength F c t (sigma alpha) (sigma beta) := by
  simpa only [m63ArcLength, one_mul] using
    integral_density_comp_monotone F c hc hsigma hmono
      (fun _ => 1) (by simpa only [one_mul] using hv) alpha beta

theorem periodic_density_comp_lift
    (hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t))
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map)
    (A : ℝ → ℝ) (hA : Continuous (fun y => A y * curveSpeed F c t y))
    (hper : Function.Periodic (fun y => A y * curveSpeed F c t y) curvePeriod)
    (q : ℝ) :
    (∫ x in q..q + curvePeriod,
      A (sigma.map x) * curveSpeed F (fun y s => c (sigma.map y) s) t x) =
      ∫ y in (0 : ℝ)..curvePeriod, A y * curveSpeed F c t y := by
  rw [integral_density_comp_monotone F c hc hsigma sigma.monotone A hA,
    sigma.period_shift]
  simpa only [zero_add] using hper.intervalIntegral_add_eq (sigma.map q) 0

theorem length_comp_lift
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun y => c y t))
    (hp : Function.Periodic (fun y => c y t) curvePeriod)
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map) :
    m62Length F (fun y s => c (sigma.map y) s) t = m62Length F c t := by
  have hv : Continuous (curveSpeed F c t) :=
    M04.continuous_pathSpeed (F.metric t) hc
  have hvelocity := m63CurveVelocity_periodic (hc.mdifferentiable one_ne_zero) hp
  have hspeed : Function.Periodic (curveSpeed F c t) curvePeriod := by
    intro x
    unfold curveSpeed
    have hvx : curveVelocity (fun y => c y t) (x + curvePeriod) =
        curveVelocity (fun y => c y t) x := hvelocity x
    have hpx : c (x + curvePeriod) t = c x t := hp x
    erw [hvx, hpx]
  simpa only [m62Length, zero_add, one_mul] using
    periodic_density_comp_lift F c (hc.mdifferentiable one_ne_zero) sigma hsigma
      (fun _ => 1) (by simpa only [one_mul] using hv)
      (by simpa only [one_mul] using hspeed) 0

end PoincareConjecture.M64
