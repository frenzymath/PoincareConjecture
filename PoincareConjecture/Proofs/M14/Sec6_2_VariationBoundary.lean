import PoincareConjecture.Proofs.M14.Sec6_2_MovingMetric
import PoincareConjecture.Proofs.M14.Sec6_2_VariationExtensions

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

noncomputable def variationBoundaryPair (V : M14LVariationData G p R) (s : ℝ) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (M14VariationField V s)

set_option backward.isDefEq.respectTransparency false in

theorem variationBoundaryPair_contDiffOn (V : M14LVariationData G p R) :
    ContDiffOn ℝ ∞ (variationBoundaryPair V) (M14SqrtParameterInterval τ₁ τ₂) := by
  have hmetric := G.spacetime.horizontalMetric.contMDiff.comp_contMDiffOn
    (R.smooth.mono R.interval_subset)
  have hpair := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ)
    (squareRoot_horizontalVelocity_smooth R) (variation_field_smooth V)
  have h : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun s => G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (M14VariationField V s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
    intro s hs
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
      using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair s hs)).2
  exact h.contDiffOn

theorem hasDerivWithinAt_variationBoundaryPair
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    HasDerivWithinAt (variationBoundaryPair V)
      (G.spacetime.horizontalMetric.inner (R.curve s)
          (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
            R.horizontal_velocity D.base_extension s) (M14VariationField V s) +
        G.spacetime.horizontalMetric.inner (R.curve s) (R.horizontal_velocity s)
          (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
            (M14VariationField V) D.variation_extension s) +
        4 * s * horizontalRicci G.leafwise (R.curve s)
          (R.horizontal_velocity s) (M14VariationField V s))
      (M14SqrtParameterInterval τ₁ τ₂) s :=
  squareRoot_covariantDerivative_metric_product R D.base_extension D.variation_extension hs

end PoincareConjecture.M14
