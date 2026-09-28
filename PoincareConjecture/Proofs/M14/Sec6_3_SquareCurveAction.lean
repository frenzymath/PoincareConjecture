import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurvePath
import PoincareConjecture.Proofs.M14.Sec6_1_SquareRootAction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem squareCurveDensity_restrict {α : ℝ → G.Point} {C D : Set ℝ}
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α C)
    (hDC : D ⊆ C) {s : ℝ} (hs : s ∈ D) (hD : UniqueDiffWithinAt ℝ D s) :
    squareCurveDensity G α D s = squareCurveDensity G α C s := by
  unfold squareCurveDensity projectedCurveVelocityWithin
  rw [mfderivWithin_subset hDC hD.uniqueMDiffWithinAt
    ((hα s (hDC hs)).mdifferentiableWithinAt (by simp))]

theorem integral_squareCurveDensity_eq_action
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {T a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (α : ℝ → G.Point) {C : Set ℝ}
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α C)
    (hsub : M14SqrtParameterInterval a b ⊆ C)
    (hclock : ∀ s ∈ M14SqrtParameterInterval a b,
      G.spacetime.timeFunction (α s) = T - s ^ 2) :
    (∫ s in Real.sqrt a..Real.sqrt b, squareCurveDensity G α C s) =
      M14BackwardLAction G (backwardPathOfSquareCurve hM12 ha hab α (hα.mono hsub) hclock) := by
  rw [backwardLAction_eq_transformed]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt hab.le)
  intro s hs
  rw [← squareCurveDensity_restrict hα hsub (Ioo_subset_Icc_self hs)
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt ha hab) s (Ioo_subset_Icc_self hs))]
  exact squareCurveDensity_eq_transformed ha (hα.mono hsub) hs

end PoincareConjecture.M14
