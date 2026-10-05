import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareCurveAction

/-!
# Prescribed endpoints for actual square-curve paths

Morgan-Tian Definition 6.7 and Proposition 6.30, pp. 108, 118-119.
The square-curve constructor retains its actual curve and velocity
while recording the proved identities of its two endpoint values.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- The actual square-curve path with its prescribed equal endpoints,
retaining the same curve and velocity, Definition 6.7, p. 108. -/
noncomputable def backwardPathOfSquareCurveBetween
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {T a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (α : ℝ → G.Point)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a b))
    (hclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (α s) = T - s ^ 2)
    {x y : G.Point} (hx : α (Real.sqrt a) = x) (hy : α (Real.sqrt b) = y) :
    M14BackwardPath G T a b x y :=
  { backwardPathOfSquareCurve hM12 ha hab α hα hclock with
    base_time := hx ▸ (backwardPathOfSquareCurve hM12 ha hab α hα hclock).base_time
    endpoint_time := hy ▸ (backwardPathOfSquareCurve hM12 ha hab α hα hclock).endpoint_time
    curve_start := hx
    curve_end := hy }

/-- Endpoint identification does not alter the actual square action,
including for a path restricted from a larger closed time domain,
equation (6.2) and Proposition 6.30, pp. 106, 118-119. -/
theorem integral_squareCurveDensity_eq_action_between
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {T a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (α : ℝ → G.Point) {C : Set ℝ}
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α C)
    (hsub : M14SqrtParameterInterval a b ⊆ C)
    (hclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (α s) = T - s ^ 2)
    {x y : G.Point} (hx : α (Real.sqrt a) = x) (hy : α (Real.sqrt b) = y) :
    (∫ s in Real.sqrt a..Real.sqrt b, squareCurveDensity G α C s) =
      M14BackwardLAction G
        (backwardPathOfSquareCurveBetween hM12 ha hab α (hα.mono hsub) hclock hx hy) :=
  integral_squareCurveDensity_eq_action hM12 ha hab α hα hsub hclock

end PoincareMT.M14
