import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.FreeBoundaryTransport
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.ChangeOfVariables
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Geometry

/-!
# Length invariance for boundary lifts with collapsed intervals

Nonnegative label derivatives suffice for the actual speed chain rule and
interval substitution. The resulting subarc and full-loop length identities
do not require an inverse label map or the shrinking-curve equation.

These are the parameter invariants in Morgan--Tian Lemma 19.6, p. 441,
used for freely parametrized annular boundaries in Lemma 19.31, pp. 464-466.
See `proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareMT.M64

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
  {t : ℝ} {sigma : ℝ → ℝ}

/-- Substitution of a continuous speed-weighted density through a monotone C1 label map,
including at zero derivative. Both interval orientations are retained; source: MT2007 Lemma
19.6, p. 441, and Lemma 19.31, pp. 464-466. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, and Lemma 19.31, pp. 464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- Actual subarc length transforms by the two label endpoints even when the monotone C1
label map has plateaus. No evolution equation is required; source: MT2007 Lemma 19.31, pp.
464-466. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, and Lemma 19.31, pp.
464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- A periodic speed-weighted density has the same integral under a monotone C1 degree-one
lift. The starting phase is arbitrary and the derivative may vanish; source: MT2007 Lemma
19.6, p. 441. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, and Lemma 19.31, pp.
464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- Periodic C1 curves have exactly the same full length after a C1
monotone degree-one boundary lift. This holds at any fixed metric slice,
including zero label derivatives, with no shrinking-flow premise.
Source: MT2007 Lemma 19.31, pp. 464-466. -/
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

end PoincareMT.M64
