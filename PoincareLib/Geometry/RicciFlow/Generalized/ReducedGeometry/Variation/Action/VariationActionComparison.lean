import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Action.VariationAction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareDensity

/-!
# Comparing a variation action with an actual square path

Morgan-Tian equation (6.2) and Lemma 6.4, pp. 106-108.
Agreement of the actual closed square curves identifies their actual
within velocities and hence their scalar and metric action densities.
The square substitution then identifies the original actions.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y x' y' : G.Point}
  {p : M14BackwardPath G T a b x y} {R : M14SquareRootPath G p}
  {q : M14BackwardPath G T a b x' y'}

private theorem inner_heq {x y : G.Point} (h : x = y)
    {v : G.Horizontal x} {w : G.Horizontal y} (hv : HEq v w) :
    G.spacetime.horizontalMetric.inner x v v = G.spacetime.horizontalMetric.inner y w w := by
  cases h
  cases hv
  rfl

/-- Agreement on the closed square interval identifies a variation's
actual action with that of a supplied path, independently of outside
values and endpoint labels, equation (6.2), p. 106. -/
theorem variationAction_eq_of_squareFamily (V : M14LVariationData G p R)
    (S : M14SquareRootPath G q) {u : ℝ} (hu : u ∈ V.parameterDomain)
    (heq : EqOn (fun r => V.squareFamily r u) S.curve (M14SqrtParameterInterval a b)) :
    M14VariationAction V u = M14BackwardLAction G q := by
  rw [variationAction_eq_squareIntegral V hu, ← integral_squareRootLIntegrand_eq_action S]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.tau_lt.le)
  intro r hr
  have hrC : r ∈ M14SqrtParameterInterval a b := Ioo_subset_Icc_self hr
  have hv := projectedCurveVelocityWithin_congrOn (G := G) heq hrC
  rw [squareRoot_projectedVelocityWithin_subset S Subset.rfl hrC
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt q.tau_nonneg q.tau_lt) r hrC)] at hv
  have hi := inner_heq (heq hrC) hv
  have hpoint : V.squareFamily r u = S.curve r := heq hrC
  change variationActionDensity V (r, u) = squareRootLIntegrand S r
  unfold variationActionDensity squareRootLIntegrand
  change 2 * r ^ 2 * horizontalScalarCurvature G.leafwise (V.squareFamily r u) +
      (1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (V.squareFamily r u)
        (projectedCurveVelocityWithin G (fun t => V.squareFamily t u)
          (M14SqrtParameterInterval a b) r)
        (projectedCurveVelocityWithin G (fun t => V.squareFamily t u)
          (M14SqrtParameterInterval a b) r) = _
  rw [hi, hpoint]

end PoincareMT.M14
