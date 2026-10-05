import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.AdaptedPullbackTrace
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.AdaptedHarnackIdentity

/-!
# The actual adapted index density in Harnack form

The backward scalar evolution removes the Laplacian and Ricci-norm
terms from the actual orthonormal trace. The remaining expression is
the boundary derivative plus the exact shifted Harnack density.
Morgan-Tian Proposition 6.43 and Claim 6.44, pp. 127-129.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p)

/-- Scalar evolution converts the actual adapted trace to the
boundary-primitive and shifted-Harnack expression, Proposition 6.43,
pp. 127-128. -/
theorem adaptedPullbackIndex_harnack (hM04 : RicciFlowCurvatureTheory.{u})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : Fin n → ∀ s, G.Horizontal (R.curve s))
    (hP : ∀ i, IsHorizontalUnitAdaptedFieldOn R (Real.sqrt a) (Real.sqrt b) (P i))
    (EP : ∀ i, M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) (P i))
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b))
    (horth : ∀ i j, G.spacetime.horizontalMetric.inner (R.curve s) (P i s) (P j s) =
      if i = j then 1 else 0)
    (hscalar : let q := spacetimeSlicePoint G.slices (R.curve s)
      let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
      M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (R.curve s) =
        -D.laplacian D.scalarCurvature q - 2 * D.ricciNormSq q) :
    (∑ i, pullbackIndexPairDensity R (horizontalAdaptedExtension (EP i))
      (horizontalAdaptedExtension (EP i)) s) =
      ((n : ℝ) - derivWithin (adaptedScalarPrimitive R) (M14SqrtParameterInterval a b) s -
        2 * s ^ 2 * (s - Real.sqrt a) ^ 2 * M14GeneralizedHarnackDensity G p
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            (p.curve t)) (s ^ 2)) / (Real.sqrt b - Real.sqrt a) ^ 2 := by
  let q := spacetimeSlicePoint G.slices (R.curve s)
  let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
  have hcancel : 4 * s ^ 2 * D.ricciNormSq q +
      2 * s ^ 2 * D.laplacian D.scalarCurvature q =
        -(2 * s ^ 2) *
          M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (R.curve s) := by
    rw [hscalar]
    ring
  rw [adaptedPullbackIndex_trace R hM04 P hP EP (Ioo_subset_Icc_self hs) horth, hcancel]
  congr 1
  linear_combination adaptedScalarPrimitive_add_shiftedHarnack hM12 R hs

end PoincareMT.M14
