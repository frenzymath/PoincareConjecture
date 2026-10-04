import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiPair
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeFirstDerivatives

/-!
# The actual horizontal paired index density

Morgan-Tian Proposition 6.13, Lemma 6.14 and Corollary 6.16,
pp. 110-112. The negative zeroth-order Jacobi terms polarize the
frozen index density. The corrected connection-time term is retained,
and the pointwise Green identity keeps the moving metric's Ricci defect.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

/-- The actual paired index density, with the negative zeroth-order
terms of the corrected Jacobi equation, Proposition 6.13 and
Corollary 6.16, pp. 110-112. -/
noncomputable def horizontalIndexPairDensity (s : ℝ)
    (Y Z DY DZ : G.Horizontal (R.curve s)) : ℝ :=
  let q := R.curve s
  let A := M14SquareRootVelocity R s
  G.spacetime.horizontalMetric.inner q DY DZ -
    horizontalRiemann G.leafwise q Y A Z A +
    2 * s * M14BcalPairing G q A Y Z +
    2 * s ^ 2 * M14HorizontalHessianPairing G q Y Z -
    4 * s * M14HorizontalRicciDerivativePairing G q Y A Z

/-- Evaluate the paired density on two fields and their actual
supplied pullback derivatives, Proposition 6.13 and Corollary 6.16,
pp. 110-112. -/
noncomputable def pullbackIndexPairDensity {Y Z : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z) (s : ℝ) : ℝ :=
  horizontalIndexPairDensity R s (Y s) (Z s)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y EY s)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z EZ s)

/-- The actual boundary pair g(DY,Z) in Green's identity,
Proposition 6.13 and Lemma 6.14, pp. 110-112. -/
noncomputable def pullbackIndexBoundaryPair {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (Z : ∀ s, G.Horizontal (R.curve s)) (s : ℝ) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve s)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y EY s)
    (Z s)

/-- The paired index density and corrected Jacobi residual sum to
the actual moving metric product expression, Lemma 6.14, pp. 110-112. -/
theorem horizontalIndexPairDensity_green_value (s : ℝ)
    (Y Z DY DZ DDY : G.Horizontal (R.curve s)) :
    horizontalIndexPairDensity R s Y Z DY DZ +
        horizontalJacobiPairResidual R s Y DY DDY Z =
      G.spacetime.horizontalMetric.inner (R.curve s) DDY Z +
        G.spacetime.horizontalMetric.inner (R.curve s) DY DZ +
        4 * s * horizontalRicci G.leafwise (R.curve s) DY Z := by
  unfold horizontalIndexPairDensity horizontalJacobiPairResidual
  ring

/-- The diagonal paired index density is exactly the frozen expanded
variation index density, Proposition 6.13 and Proposition 6.33,
pp. 110-112, 120-121. -/
theorem secondVariationIndexDensity_eq_pair
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V) (s : ℝ) :
    M14SecondVariationIndexDensity V D s =
      pullbackIndexPairDensity R D.variation_extension D.variation_extension s := by
  let q := R.curve s
  let A := M14SquareRootVelocity R s
  let Y := M14VariationField V s
  have hR : horizontalRiemann G.leafwise q Y A Y A =
      -horizontalRiemann G.leafwise q Y A A Y :=
    (G.leafwise.sliceConnection (G.spacetime.timeFunction q)).curvatureTensor_swap_last _ _ _ _ _
  unfold M14SecondVariationIndexDensity pullbackIndexPairDensity horizontalIndexPairDensity
  dsimp only
  change _ = _ - horizontalRiemann G.leafwise q Y A Y A + _ + _ - _
  rw [hR]
  unfold M14BcalPairing
  ring

end PoincareMT.M14
