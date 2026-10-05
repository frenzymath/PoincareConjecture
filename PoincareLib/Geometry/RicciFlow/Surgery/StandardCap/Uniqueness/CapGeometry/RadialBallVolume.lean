import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.RadialBallDiameter
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Calibration.Calibration

local notation "M10.euclideanVolumeCalibration_smul_hausdorff" => PoincareMT.ReducedVolume.euclideanVolumeCalibration_smul_hausdorff

/-!
# Actual radial cap volume from its contracting coordinates

Morgan-Tian Theorem 12.32, pp. 326-327. The genuine inverse-arclength
map is globally 1-Lipschitz and maps the Euclidean ball exactly onto the
radial cap carrier. The frozen calibrated Hausdorff measure therefore
has the ordinary Euclidean volume as an upper bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M35.Uniqueness

local notation "V" => StandardCapSpace

variable (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : V,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)

include D hsec hrotation hcomplete

/-- Theorem 12.32: the actual radial carrier's calibrated volume
is bounded by the Euclidean ball of its true radius. -/
theorem radial_ball_volume_le (P : M35StandardCapPredecessors) (R : ℝ) :
    calibratedMetricVolume g (g.ball 0 R) ≤ volume (Metric.ball (0 : V) R) := by
  let f := intrinsicSpatialInverse g hrotation hcomplete
  have hlip : @LipschitzWith V V inferInstance
      g.toEMetricSpace.toPseudoEMetricSpace 1 f := by
    intro x y
    change g.edist (f x) (f y) ≤ (1 : ℝ≥0∞) * edist x y
    rw [one_mul]
    exact intrinsicSpatialInverse_edist_le g D hrotation hcomplete hsec x y
  have hhaus := @LipschitzWith.hausdorffMeasure_image_le V V
    (inferInstance : EMetricSpace V) g.toEMetricSpace
    inferInstance inferInstance inferInstance inferInstance 1 f hlip
    (3 : ℝ) (by norm_num) (Metric.ball (0 : V) R)
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hhaus
  have hcal := congrArg (fun mu : Measure V => mu (Metric.ball (0 : V) R))
    (M10.euclideanVolumeCalibration_smul_hausdorff 3)
  calc
    calibratedMetricVolume g (g.ball 0 R) =
        euclideanVolumeCalibration 3 *
          @Measure.hausdorffMeasure V g.toEMetricSpace inferInstance inferInstance
            (3 : ℝ) (f '' Metric.ball (0 : V) R) := by
      rw [← intrinsicSpatialInverse_image_ball g hrotation hcomplete P R]
      rfl
    _ ≤ euclideanVolumeCalibration 3 *
        Measure.hausdorffMeasure (3 : ℝ) (Metric.ball (0 : V) R) :=
      mul_le_mul' le_rfl hhaus
    _ = volume (Metric.ball (0 : V) R) := by
      simpa only [Measure.smul_apply, smul_eq_mul, Nat.cast_ofNat] using hcal

theorem radial_ball_volume_lt_top (P : M35StandardCapPredecessors) (R : ℝ) :
    calibratedMetricVolume g (g.ball 0 R) < ⊤ :=
  (radial_ball_volume_le g D hrotation hcomplete hsec P R).trans_lt
    measure_ball_lt_top

end PoincareMT.M35.Uniqueness
