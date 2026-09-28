import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveAction









set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



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

end PoincareConjecture.M14
