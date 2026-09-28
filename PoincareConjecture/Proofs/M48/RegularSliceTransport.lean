import PoincareConjecture.Proofs.M48.RegularSpacetime
import PoincareConjecture.Proofs.M13.GeneralizedSlices

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PoincareConjecture

variable (P : M48Predecessors.{u}) {F : SurgeryFlowData.{u}} {T : ℝ}
  {L : RepairedPreterminalSlab F T} (R : M48RegularSpacetimeData L)

include P

theorem M48Predecessors.regular_scalar (t : ℝ) (ht : t ∈ R.history.generalized.interval)
    (x : (R.history.generalized.slice t).carrier) :
    horizontalScalarCurvature R.geometry.leafwise (⟨t, x⟩ : R.history.generalized.point) =
      (F.connection t).scalarCurvature (R.history.history.forward t ht x) :=
  (Proofs.M13.originalSlice_scalar R.geometry P.m13 t x).trans
    (R.history.scalar_pullback t ht x).symm

theorem M48Predecessors.regular_curvatureNorm (t : ℝ)
    (ht : t ∈ R.history.generalized.interval) (x : (R.history.generalized.slice t).carrier) :
    horizontalCurvatureNorm R.geometry.leafwise (⟨t, x⟩ : R.history.generalized.point) =
      (F.connection t).curvatureTensorNorm (R.history.history.forward t ht x) :=
  (Proofs.M13.originalSlice_curvatureNorm R.geometry P.m13 t x).trans
    (R.history.curvature_norm_pullback t ht x).symm

theorem M48Predecessors.regular_negativePart (t : ℝ)
    (ht : t ∈ R.history.generalized.interval) (x : (R.history.generalized.slice t).carrier) :
    (R.geometry.leafwise.sliceConnection t).negativeCurvaturePart
      ((R.geometry.sliceIdentification t).identification x) =
        (F.connection t).negativeCurvaturePart (R.history.history.forward t ht x) :=
  (Proofs.M13.originalSlice_negativePart R.geometry P.m13 t x).trans
    (R.history.negative_part_pullback t ht x).symm

theorem M48Predecessors.regular_volume (t : ℝ) (ht : t ∈ R.history.generalized.interval)
    (U : Set (R.history.generalized.slice t).carrier) :
    calibratedMetricVolume (R.geometry.realization.slices t).metricOnPoints
      ((R.geometry.sliceIdentification t).identification '' U) =
        calibratedMetricVolume (F.metric t) (R.history.history.forward t ht '' U) :=
  (Proofs.M13.originalSlice_volume R.geometry P.m13 t U).trans
    (R.history.volume_image t ht U).symm

theorem M48Predecessors.regular_edist (t : ℝ) (ht : t ∈ R.history.generalized.interval)
    (hregular : t ∉ F.surgery_times) (x y : (R.history.generalized.slice t).carrier) :
    (R.geometry.realization.slices t).metricOnPoints.edist
      ((R.geometry.sliceIdentification t).identification x)
      ((R.geometry.sliceIdentification t).identification y) =
        (F.metric t).edist (R.history.history.forward t ht x)
          (R.history.history.forward t ht y) :=
  (Proofs.M13.originalSlice_edist R.geometry P.m13 t x y).trans
    (R.history.regular_distance t ht hregular x y).symm

end PoincareConjecture
