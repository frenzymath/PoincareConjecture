import PoincareConjecture.Definitions.M12HorizontalCalculus
import PoincareConjecture.Statements.M12MetricPredecessors
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

theorem M12MetricPredecessors.exists_leafwiseLeviCivitaFamily
    (h : M12MetricPredecessors.{u} n) (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) :
    Nonempty (LeafwiseLeviCivitaFamily F S) := by
  classical
  exact ⟨⟨fun t ↦ (h.connection_exists (S t).Point (S t).metricOnPoints).some⟩⟩

namespace LeafwiseLeviCivitaFamily

variable (D D' : LeafwiseLeviCivitaFamily F S)

theorem horizontalRiemann_eq (p : F.Point) (u v w z : F.Horizontal p) :
    horizontalRiemann D p u v w z = horizontalRiemann D' p u v w z := by
  exact (D.sliceConnection (F.timeFunction p)).curvatureTensor_eq
    (D'.sliceConnection (F.timeFunction p)) _ _ _ _ _

theorem horizontalRicci_eq (p : F.Point) (u v : F.Horizontal p) :
    horizontalRicci D p u v = horizontalRicci D' p u v := by
  simp only [horizontalRicci, LeviCivitaData.ricci,
    (D.sliceConnection (F.timeFunction p)).curvatureTensor_eq
      (D'.sliceConnection (F.timeFunction p))]

theorem horizontalScalarCurvature_eq (p : F.Point) :
    horizontalScalarCurvature D p = horizontalScalarCurvature D' p := by
  simp only [horizontalScalarCurvature, LeviCivitaData.scalarCurvature,
    LeviCivitaData.ricci,
    (D.sliceConnection (F.timeFunction p)).curvatureTensor_eq
      (D'.sliceConnection (F.timeFunction p))]

theorem horizontalCurvatureNorm_eq (p : F.Point) :
    horizontalCurvatureNorm D p = horizontalCurvatureNorm D' p := by
  exact (D.sliceConnection (F.timeFunction p)).curvatureTensorNorm_eq
    (D'.sliceConnection (F.timeFunction p)) _

theorem horizontalCurvatureNormSq_eq (p : F.Point) :
    horizontalCurvatureNormSq D p = horizontalCurvatureNormSq D' p := by
  rw [horizontalCurvatureNormSq, horizontalCurvatureNormSq, D.horizontalCurvatureNorm_eq D']

theorem intrinsicGeneralizedRicciEquation_iff :
    IntrinsicGeneralizedRicciEquation D ↔ IntrinsicGeneralizedRicciEquation D' := by
  simp only [IntrinsicGeneralizedRicciEquation, D.horizontalRicci_eq D']

theorem horizontalRicci_symmetric (h : M12MetricPredecessors.{u} n)
    (p : F.Point) (u v : F.Horizontal p) :
    horizontalRicci D p u v = horizontalRicci D p v u := by
  let t := F.timeFunction p
  let x := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  exact ((h.curvature_calculus (S t).Point (S t).metricOnPoints
    (D.sliceConnection t)).2.2.2.1 x (j.symm u) (j.symm v) 0 0).2.2.2

end LeafwiseLeviCivitaFamily

theorem horizontalMetricLieDerivativeOnFields_symmetric
    (V W : HorizontalSection F) (p : F.Point) :
    horizontalMetricLieDerivativeOnFields F V W p =
      horizontalMetricLieDerivativeOnFields F W V p := by
  have h : (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) =
      (fun q ↦ F.horizontalMetric.inner q (W q) (V q)) :=
    funext fun q ↦ F.horizontalMetric.symm q _ _
  unfold horizontalMetricLieDerivativeOnFields
  rw [h, F.horizontalMetric.symm p (horizontalTimeBracket F V p) (W p),
    F.horizontalMetric.symm p (V p) (horizontalTimeBracket F W p)]
  ring

theorem horizontalMetricLieDerivative_symmetric (p : F.Point) (u v : F.Horizontal p) :
    horizontalMetricLieDerivative F p u v = horizontalMetricLieDerivative F p v u :=
  horizontalMetricLieDerivativeOnFields_symmetric _ _ p

end PoincareConjecture
