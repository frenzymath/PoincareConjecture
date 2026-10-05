import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Curve.Lift

/-!
# Exact scalar curve geometry under a constant auxiliary lift

The checked velocity and curvature-vector identities, together with the
literal section metric, preserve the actual scalar densities and all
parameter subarc integrals. Source: MT2007 Section 19.3 and Lemma 19.31,
pp. 445-446 and 464-466; ramp transport approximation derivation.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- A constant auxiliary lift preserves immersion.
Source: MT Lemma 19.31, pp. 464-466; exact constant-lift derivation. -/
theorem constantLift_immersed
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    ∀ x, curveVelocity (n := n + 1) (auxiliaryCircleSection P q ∘ gamma) x ≠ 0 := by
  intro x hx
  have hsplit := auxiliaryCircle_curveVelocity_split P q
    (hgamma.mdifferentiableAt (by norm_num) (x := x))
  rw [hx, map_zero] at hsplit
  exact himm x (congrArg Prod.fst hsplit).symm

/-- A constant auxiliary lift preserves the actual curvature norm.
Source: MT Lemma 19.31, pp. 464-466; exact constant-lift derivation. -/
theorem constantLift_curvature
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) (x : ℝ) :
    m62Curvature P.flow (fun y _ => auxiliaryCircleSection P q (gamma y)) time x =
      m62Curvature F (fun y _ => gamma y) time x := by
  unfold m62Curvature m62CurvatureSquared
  rw [auxiliaryCircle_curvatureVector_eq P q (fun y _ => gamma y) time hgamma himm x]
  exact congrArg Real.sqrt (auxiliaryCircle_section_metric P time q _ _ _)

/-- Literal parameter subarc lengths are unchanged by a constant lift.
Source: MT Lemma 19.31, pp. 464-466; exact constant-lift derivation. -/
theorem constantLift_arcLength
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (alpha beta : ℝ) :
    m63ArcLength P.flow (fun y _ => auxiliaryCircleSection P q (gamma y))
        time alpha beta = m63ArcLength F (fun y _ => gamma y) time alpha beta := by
  unfold m63ArcLength
  apply intervalIntegral.integral_congr
  intro x _hx
  exact auxiliaryCircle_curveSpeed_eq P q (fun y _ => gamma y) time x
    (hgamma.mdifferentiableAt (by norm_num))

/-- Full-period length is unchanged by a constant auxiliary lift.
Source: MT Lemma 19.31, pp. 464-466; exact constant-lift derivation. -/
theorem constantLift_length
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma) :
    m62Length P.flow (fun y _ => auxiliaryCircleSection P q (gamma y)) time =
      m62Length F (fun y _ => gamma y) time :=
  constantLift_arcLength P q time hgamma 0 curvePeriod

/-- Constant lifting preserves absolute turning on every parameter subarc.
Source: MT Lemma 19.31, pp. 464-466; exact constant-lift derivation. -/
theorem constantLift_arcTotalCurvature
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) (alpha beta : ℝ) :
    m63ArcTotalCurvature P.flow (fun y _ => auxiliaryCircleSection P q (gamma y))
        time alpha beta =
      m63ArcTotalCurvature F (fun y _ => gamma y) time alpha beta := by
  unfold m63ArcTotalCurvature
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only
  rw [constantLift_curvature P q time hgamma himm x,
    auxiliaryCircle_curveSpeed_eq P q (fun y _ => gamma y) time x
      (hgamma.mdifferentiableAt (by norm_num))]

/-- Full-period total curvature is unchanged by a constant lift.
Source: MT Lemma 19.31, pp. 464-466; exact constant-lift derivation. -/
theorem constantLift_totalCurvature
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    m62TotalCurvature P.flow (fun y _ => auxiliaryCircleSection P q (gamma y)) time =
      m62TotalCurvature F (fun y _ => gamma y) time :=
  constantLift_arcTotalCurvature P q time hgamma himm 0 curvePeriod

end PoincareMT.M64.RampTransport
