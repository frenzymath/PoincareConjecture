import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.MovingMetric
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Fields.VariationExtensions

/-!
# The smooth boundary pair in first variation

Morgan-Tian Lemma 6.4, pp. 107-108. The actual pairing of the base
square-root velocity and the variation field is smooth on the closed
interval. Its within derivative includes the +4s Ricci metric defect.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

/-- The boundary pairing in square-root first variation,
Lemma 6.4 and equation (6.2), pp. 106-108. -/
noncomputable def variationBoundaryPair (V : M14LVariationData G p R) (s : ℝ) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (M14VariationField V s)

set_option backward.isDefEq.respectTransparency false in
-- Bundle evaluation and the scalar pairing unfold to the same selected metric.
/-- The boundary pairing is smooth within the full closed interval,
including an initial square-root time zero, Lemma 6.4, pp. 107-108. -/
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

/-- The actual boundary-pair derivative has the +4s Ricci defect,
at every closed time point, Lemma 6.4, pp. 107-108. -/
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

end PoincareMT.M14
