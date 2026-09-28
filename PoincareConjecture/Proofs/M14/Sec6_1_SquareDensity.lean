import PoincareConjecture.Proofs.M14.Sec6_1_SquareRootAction
import PoincareConjecture.Proofs.M14.Sec6_2_SquareCurve
import PoincareConjecture.Proofs.M14.Sec6_3_SquareRootComparison

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem inner_heq {x y : G.Point} (h : x = y)
    {v : G.Horizontal x} {w : G.Horizontal y} (hv : HEq v w) :
    G.spacetime.horizontalMetric.inner x v v = G.spacetime.horizontalMetric.inner y w w := by
  cases h
  cases hv
  rfl

theorem squareRootLIntegrand_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
    (R : M14SquareRootPath G p) :
    ContDiffOn ℝ ∞ (squareRootLIntegrand R) (M14SqrtParameterInterval a b) := by
  apply (squareCurveDensity_contDiffOn hM12
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt))
    (R.smooth.mono R.interval_subset)).congr
  intro s hs
  simp only [squareRootLIntegrand, squareCurveDensity,
    squareRoot_horizontalVelocity_eq_projection R hs, projectedCurveVelocityWithin,
    M14SqrtParameterInterval]

theorem squareRootLIntegrand_eq_on_subset
    {T₁ T₂ a b c d : ℝ} {x₁ y₁ x₂ y₂ : G.Point}
    {p : M14BackwardPath G T₁ a b x₁ y₁} {q : M14BackwardPath G T₂ c d x₂ y₂}
    (R : M14SquareRootPath G p) (S : M14SquareRootPath G q) {K : Set ℝ}
    (hKR : K ⊆ M14SqrtParameterInterval a b) (hKS : K ⊆ M14SqrtParameterInterval c d)
    (heq : EqOn R.curve S.curve K) {s : ℝ} (hs : s ∈ K)
    (hK : UniqueDiffWithinAt ℝ K s) : squareRootLIntegrand R s = squareRootLIntegrand S s := by
  have hv := squareRoot_horizontalVelocity_heq_on_subset R S hKR hKS heq hs hK
  have hinner := inner_heq (G := G) (heq hs) hv
  unfold squareRootLIntegrand
  rw [hinner, heq hs]

end PoincareConjecture.M14
