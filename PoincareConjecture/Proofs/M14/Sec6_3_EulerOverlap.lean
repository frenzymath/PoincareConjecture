import PoincareConjecture.Proofs.M14.Sec6_2_SquareRepresentative
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackRestriction
import PoincareConjecture.Proofs.M14.Sec6_3_SquareRootComparison










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b T' c d : ℝ} {x y x' y' : G.Point}
  {p : M14BackwardPath G T a b x y} {q : M14BackwardPath G T' c d x' y'}

private theorem residualPair_heq {x y : G.Point} (h : x = y)
    {A V W : G.Horizontal x} {A' V' W' : G.Horizontal y}
    (hA : HEq A A') (hV : HEq V V') (hW : HEq W W') (s : ℝ) :
    G.spacetime.horizontalMetric.inner x A W -
        2 * s ^ 2 * M14HorizontalScalarDifferential G x W.val +
        4 * s * horizontalRicci G.leafwise x V W =
      G.spacetime.horizontalMetric.inner y A' W' -
        2 * s ^ 2 * M14HorizontalScalarDifferential G y W'.val +
        4 * s * horizontalRicci G.leafwise y V' W' := by
  cases h
  cases hA
  cases hV
  cases hW
  rfl




theorem squareRootEulerResidual_eq_on_subset
    (R : M14SquareRootPath G p) (S : M14SquareRootPath G q)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b)
      R.horizontal_velocity)
    (F : M14PullbackExtension G S.curve (M14SqrtParameterInterval c d)
      S.horizontal_velocity) {K : Set ℝ}
    (hKR : K ⊆ M14SqrtParameterInterval a b) (hKS : K ⊆ M14SqrtParameterInterval c d)
    (hK : UniqueDiffOn ℝ K) (heq : EqOn R.curve S.curve K)
    {s : ℝ} (hs : s ∈ K) {W : G.Horizontal (R.curve s)}
    {W' : G.Horizontal (S.curve s)} (hW : HEq W W') :
    M14SquareRootEulerResidual G R E s W = M14SquareRootEulerResidual G S F s W' := by
  have hvel (r : ℝ) (hr : r ∈ K) :=
    squareRoot_horizontalVelocity_heq_on_subset R S hKR hKS heq hr (hK r hr)
  let E₀ := pullbackExtensionRestrict E hKR
  let F₀ := pullbackExtensionRestrict F hKS
  let E₁ := pullbackExtensionCongrOn E₀ heq hvel
  have hR := ((R.smooth.mono R.interval_subset) s (hKR hs)).mdifferentiableWithinAt
    (by simp)
  have hS := ((S.smooth.mono S.interval_subset) s (hKS hs)).mdifferentiableWithinAt
    (by simp)
  have hDR := horizontalCovariantDerivative_restrict_subset E hKR (hK s hs) hR
  have hDS := horizontalCovariantDerivative_restrict_subset F hKS (hK s hs) hS
  have hDE := horizontalCovariantDerivative_congrOn E₀ heq hvel hs
  have hEF := horizontalCovariantDerivative_extension_independent E₁ F₀ hs (hK s hs)
    (hS.mono hKS)
  have hD : HEq (M14HorizontalCovariantDerivative G R.curve
      (M14SqrtParameterInterval a b) R.horizontal_velocity E s)
      (M14HorizontalCovariantDerivative G S.curve
        (M14SqrtParameterInterval c d) S.horizontal_velocity F s) := by
    rw [hDR, hDS]
    exact hDE.trans (heq_of_eq hEF)
  exact residualPair_heq (G := G) (heq hs) hD (hvel s hs) hW s

end PoincareConjecture.M14
