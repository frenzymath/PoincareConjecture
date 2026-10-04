import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedRicci
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.SliceGeometry.PinchingIsometry

/-!
# Metric calculus on the original generalized-flow slices

Use the retained M11 slice identification and the supplied M13 theorem at
scale one. Both metrics and connections are the specified ones. In
particular, the resulting horizontal curvature is that of the original
generalized flow at the same point. No realization is reselected.
Source: Morgan--Tian Theorem 1.2, pp. 3-7, and Definition 3.35, pp. 60-61.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.EpochExtension.SliceGeometry

variable {F : GeneralizedRicciFlowData.{u}}
  (G : Spacetime.FlowBoxRicciGeometry F)

/-- The selected identification lands at the literal point `(t,x)`. -/
theorem originalSlice_point (t : ℝ) (x : (F.slice t).carrier) :
    (G.sliceIdentification t).identification x =
      spacetimeSlicePoint G.realization.slices (⟨t, x⟩ : F.point) := by
  apply Subtype.ext
  exact (G.sliceIdentification t).identification_eq x

/-- The exact retained slice identification is a unit-scale homothety. -/
theorem originalSlice_homothety (t : ℝ) :
    MetricHomothety (F.metric t) (G.realization.slices t).metricOnPoints
      (G.sliceIdentification t).identification 1 := by
  intro x v w
  simpa only [Spacetime.flowSliceLabel, one_mul] using (G.sliceIdentification t).metric_eq x v w

/-- Apply the supplied M13 calculus to these fixed metrics and this fixed map. -/
theorem originalSlice_calculus (h : GeneralizedParabolicRescalingTheory.{u} 3) (t : ℝ) :
    MetricHomothetyCalculus (F.metric t) (G.realization.slices t).metricOnPoints
      (G.sliceIdentification t).identification 1 :=
  h.metric_homothety (F.slice t).carrier (G.realization.slices t).Point
    (F.metric t) (G.realization.slices t).metricOnPoints
    (G.sliceIdentification t).identification 1 zero_lt_one (originalSlice_homothety G t)

variable (h : GeneralizedParabolicRescalingTheory.{u} 3)
include h

theorem originalSlice_scalar (t : ℝ) (x : (F.slice t).carrier) :
    horizontalScalarCurvature G.leafwise (⟨t, x⟩ : F.point) =
      (F.connection t).scalarCurvature x := by
  have H := (originalSlice_calculus G h t).scalar_eq
    (F.connection t) (G.leafwise.sliceConnection t) x
  exact (congrArg (G.leafwise.sliceConnection t).scalarCurvature
    (originalSlice_point G t x)).symm.trans (by simpa only [div_one, Spacetime.flowSliceLabel] using H)

theorem originalSlice_curvatureNorm (t : ℝ) (x : (F.slice t).carrier) :
    horizontalCurvatureNorm G.leafwise (⟨t, x⟩ : F.point) =
      (F.connection t).curvatureTensorNorm x := by
  have H := (originalSlice_calculus G h t).curvature_norm_eq
    (F.connection t) (G.leafwise.sliceConnection t) x
  exact (congrArg (G.leafwise.sliceConnection t).curvatureTensorNorm
    (originalSlice_point G t x)).symm.trans (by simpa only [div_one, Spacetime.flowSliceLabel] using H)

theorem originalSlice_negativePart (t : ℝ) (x : (F.slice t).carrier) :
    (G.leafwise.sliceConnection t).negativeCurvaturePart
      ((G.sliceIdentification t).identification x) =
        (F.connection t).negativeCurvaturePart x :=
  negativeCurvaturePart_eq_one (originalSlice_calculus G h t)
    (originalSlice_homothety G t) (F.connection t) (G.leafwise.sliceConnection t) x

theorem originalSlice_edist (t : ℝ) (x y : (F.slice t).carrier) :
    (G.realization.slices t).metricOnPoints.edist
      ((G.sliceIdentification t).identification x)
      ((G.sliceIdentification t).identification y) = (F.metric t).edist x y := by
  simpa [Spacetime.flowSliceLabel] using (originalSlice_calculus G h t).edist_eq x y

theorem originalSlice_ball (t : ℝ) (x : (F.slice t).carrier) (r : ℝ) :
    (G.sliceIdentification t).identification '' (F.metric t).ball x r =
      (G.realization.slices t).metricOnPoints.ball
        ((G.sliceIdentification t).identification x) r := by
  simpa [Spacetime.flowSliceLabel] using (originalSlice_calculus G h t).ball_image x r

theorem originalSlice_complete (t : ℝ) :
    MetricComplete (G.realization.slices t).metricOnPoints ↔ MetricComplete (F.metric t) :=
  (originalSlice_calculus G h t).complete_iff

theorem originalSlice_volume (t : ℝ) (U : Set (F.slice t).carrier) :
    calibratedMetricVolume (G.realization.slices t).metricOnPoints
      ((G.sliceIdentification t).identification '' U) =
        calibratedMetricVolume (F.metric t) U := by
  simpa [Spacetime.flowSliceLabel] using (originalSlice_calculus G h t).volume_image U

end PoincareMT.EpochExtension.SliceGeometry
