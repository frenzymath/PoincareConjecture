import PoincareConjecture.Definitions.M12HorizontalCalculus
import PoincareConjecture.Statements.Ch01.CurvatureCalculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

structure SpacetimeHorizontalConnection (D : LeafwiseLeviCivitaFamily F S) where
  connection : CovariantDerivative (spacetimeModel n) (EuclideanSpace ℝ (Fin n))
    F.Horizontal
  smooth : CovariantDerivative.ContMDiffCovariantDerivative connection ∞
  local_smooth : ∀ U : Set F.Point, IsOpen U →
    ContMDiffCovariantDerivativeOn (I := spacetimeModel n) (V := F.Horizontal)
      (EuclideanSpace ℝ (Fin n)) ∞ connection.toFun U
  raw_eq : ∀ U : Set F.Point, IsOpen U →
    ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
      ∀ p ∈ U, connection V p = rawHorizontalCovariantDerivative D V p
  time_eq : ∀ U : Set F.Point, IsOpen U →
    ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
      ∀ p ∈ U, (connection V p (F.timeVector p)).val =
        VectorField.mlieBracket (spacetimeModel n)
          (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
          (horizontalSectionVectorField F V) p
  horizontal_eq : ∀ U : Set F.Point, IsOpen U →
    ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
      ∀ p ∈ U, ∀ v : F.Horizontal p,
        connection V p v.val = rawLeafwiseCovariantDerivative D V p v
  metric_defect : ∀ U : Set F.Point, IsOpen U →
    ∀ V W : HorizontalSection F,
      IsSmoothHorizontalSectionOn F V U → IsSmoothHorizontalSectionOn F W U →
      ∀ p ∈ U, ∀ Z : TangentSpace (spacetimeModel n) p,
        mvfderiv (spacetimeModel n)
            (fun q : F.Point ↦ F.horizontalMetric.inner q (V q) (W q)) p Z -
          F.horizontalMetric.inner p (connection V p Z) (W p) -
          F.horizontalMetric.inner p (V p) (connection W p Z) =
        (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p Z) *
          horizontalMetricLieDerivative F p (V p) (W p)

structure HorizontalRicciCalculus (D : LeafwiseLeviCivitaFamily F S) : Prop where
  lie_tensor : IsSmoothHorizontalCovariantTensor F (k := 2)
    (fun p v ↦ horizontalMetricLieDerivative F p (v 0) (v 1))
  lie_symmetric : ∀ p : F.Point, ∀ u v : F.Horizontal p,
    horizontalMetricLieDerivative F p u v = horizontalMetricLieDerivative F p v u
  lie_on_fields : ∀ U : Set F.Point, IsOpen U →
    ∀ V W : HorizontalSection F,
      IsSmoothHorizontalSectionOn F V U → IsSmoothHorizontalSectionOn F W U →
      ∀ p ∈ U, horizontalMetricLieDerivative F p (V p) (W p) =
        horizontalMetricLieDerivativeOnFields F V W p
  time_bracket_horizontal : ∀ U : Set F.Point, IsOpen U →
    ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
      ∀ p ∈ U, mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p
        (VectorField.mlieBracket (spacetimeModel n)
          (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
          (horizontalSectionVectorField F V) p) = 0
  riemann_tensor : IsSmoothHorizontalCovariantTensor F (k := 4)
    (fun p v ↦ horizontalRiemann D p (v 0) (v 1) (v 2) (v 3))
  ricci_tensor : IsSmoothHorizontalCovariantTensor F (k := 2)
    (fun p v ↦ horizontalRicci D p (v 0) (v 1))
  ricci_symmetric : ∀ p : F.Point, ∀ u v : F.Horizontal p,
    horizontalRicci D p u v = horizontalRicci D p v u
  scalar_smooth : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalScalarCurvature D)
  normSq_smooth : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalCurvatureNormSq D)
  norm_continuous : Continuous (horizontalCurvatureNorm D)
  slice_calculus : ∀ t : ℝ, (D.sliceConnection t).CurvatureTensorCalculus
  riemann_choice : ∀ D' : LeafwiseLeviCivitaFamily F S,
    ∀ p : F.Point, ∀ u v w z : F.Horizontal p,
      horizontalRiemann D p u v w z = horizontalRiemann D' p u v w z
  ricci_choice : ∀ D' : LeafwiseLeviCivitaFamily F S,
    ∀ p : F.Point, ∀ u v : F.Horizontal p,
      horizontalRicci D p u v = horizontalRicci D' p u v
  scalar_choice : ∀ D' : LeafwiseLeviCivitaFamily F S, ∀ p : F.Point,
    horizontalScalarCurvature D p = horizontalScalarCurvature D' p
  norm_choice : ∀ D' : LeafwiseLeviCivitaFamily F S, ∀ p : F.Point,
    horizontalCurvatureNorm D p = horizontalCurvatureNorm D' p
  normSq_choice : ∀ D' : LeafwiseLeviCivitaFamily F S, ∀ p : F.Point,
    horizontalCurvatureNormSq D p = horizontalCurvatureNormSq D' p
  equation_choice : ∀ D' : LeafwiseLeviCivitaFamily F S,
    IntrinsicGeneralizedRicciEquation D ↔ IntrinsicGeneralizedRicciEquation D'
  leafwise_smooth : ∀ U : Set F.Point, IsOpen U →
    ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
      ContMDiffOn (spacetimeModel n)
        ((spacetimeModel n).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
        (fun p : F.Point ↦ Bundle.TotalSpace.mk'
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (E := fun q : F.Point ↦ F.Horizontal q →L[ℝ] F.Horizontal q)
          p (rawLeafwiseCovariantDerivative D V p)) U
  leafwise_apply_smooth : ∀ U : Set F.Point, IsOpen U →
    ∀ V W : HorizontalSection F,
      IsSmoothHorizontalSectionOn F V U → IsSmoothHorizontalSectionOn F W U →
      IsSmoothHorizontalSectionOn F (fun p ↦ rawLeafwiseCovariantDerivative D W p (V p)) U
  leafwise_choice : ∀ D' : LeafwiseLeviCivitaFamily F S,
    ∀ U : Set F.Point, IsOpen U →
      ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
        ∀ p ∈ U, rawLeafwiseCovariantDerivative D V p =
          rawLeafwiseCovariantDerivative D' V p
  horizontal_choice : ∀ D' : LeafwiseLeviCivitaFamily F S,
    ∀ U : Set F.Point, IsOpen U →
      ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
        ∀ p ∈ U, rawHorizontalCovariantDerivative D V p =
          rawHorizontalCovariantDerivative D' V p
  horizontal_connection : Nonempty (SpacetimeHorizontalConnection D)

end PoincareConjecture
