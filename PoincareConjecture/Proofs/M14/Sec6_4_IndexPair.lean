import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPair
import PoincareConjecture.Proofs.M14.Sec6_4_GaugeFirstDerivatives










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)




noncomputable def horizontalIndexPairDensity (s : ℝ)
    (Y Z DY DZ : G.Horizontal (R.curve s)) : ℝ :=
  let q := R.curve s
  let A := M14SquareRootVelocity R s
  G.spacetime.horizontalMetric.inner q DY DZ -
    horizontalRiemann G.leafwise q Y A Z A +
    2 * s * M14BcalPairing G q A Y Z +
    2 * s ^ 2 * M14HorizontalHessianPairing G q Y Z -
    4 * s * M14HorizontalRicciDerivativePairing G q Y A Z




noncomputable def pullbackIndexPairDensity {Y Z : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z) (s : ℝ) : ℝ :=
  horizontalIndexPairDensity R s (Y s) (Z s)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y EY s)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z EZ s)



noncomputable def pullbackIndexBoundaryPair {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (Z : ∀ s, G.Horizontal (R.curve s)) (s : ℝ) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve s)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y EY s)
    (Z s)



theorem horizontalIndexPairDensity_green_value (s : ℝ)
    (Y Z DY DZ DDY : G.Horizontal (R.curve s)) :
    horizontalIndexPairDensity R s Y Z DY DZ +
        horizontalJacobiPairResidual R s Y DY DDY Z =
      G.spacetime.horizontalMetric.inner (R.curve s) DDY Z +
        G.spacetime.horizontalMetric.inner (R.curve s) DY DZ +
        4 * s * horizontalRicci G.leafwise (R.curve s) DY Z := by
  unfold horizontalIndexPairDensity horizontalJacobiPairResidual
  ring




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

end PoincareConjecture.M14
