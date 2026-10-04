import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.ArclengthTimeIntegral
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.RadialUnitRicci
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The radial velocity is the actual arclength time derivative

Morgan-Tian Section 12.6, pp. 309-313, and the corrected radial-gauge
erratum. Differentiate the genuine arclength integral in the raw fixed
coordinates. Its radial Ricci trace and actual change of arclength variable
identify the result with the constructed intrinsic velocity, exactly once.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)

/-- The actual radial Ricci trace is the constructed intrinsic
acceleration, multiplied by the genuine change-of-variable speed. -/
theorem rawAxisSpeedTimeDerivative_eq_intrinsic {t : ℝ}
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (G.flow.metric t).inner x u v)
    (hcomplete : MetricComplete (G.flow.metric t)) {r : ℝ} (hr : 0 < r) :
    rawAxisSpeedTimeDerivative G t r =
      intrinsicRadialAcceleration (G.flow.metric t) hrotation hcomplete
        (radialArclength (G.flow.metric t) r) * axisRadialSpeed (G.flow.metric t) r := by
  let g := G.flow.metric t
  have hpos : 0 < radialArclength g r := by
    simpa only [radialArclength_zero] using (radialArclength_strictMono g) hr
  have hinv : (radialArclengthOrderIso g hrotation hcomplete).symm
      (radialArclength g r) = r :=
    (radialArclengthOrderIso g hrotation hcomplete).symm_apply_apply r
  rw [rawAxisSpeedTimeDerivative,
    rotational_axis_radial_ricci (G.flow.connection t) hrotation hr,
    intrinsicRadialAcceleration_eq_sectional g hrotation hcomplete hpos, hinv]
  unfold axisRadialSpeed
  change -(2 * radialMixedCurvatureFactor g r) / Real.sqrt (axisRadialCoefficient g r) =
    -2 * (radialMixedCurvatureFactor g r / axisRadialCoefficient g r) *
      Real.sqrt (axisRadialCoefficient g r)
  field_simp [(axisRadialCoefficient_pos g r).ne',
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne']
  rw [Real.sq_sqrt (axisRadialCoefficient_pos g r).le]

/-- The moving arclength speed is exactly v in the corrected gauge
equation; it is not an independently supplied drift coefficient. -/
theorem raw_radialArclength_hasDerivAt_velocity {t : ℝ}
    (ht : t ∈ Ioo 0 G.lifetime)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (G.flow.metric t).inner x u v)
    (hcomplete : MetricComplete (G.flow.metric t)) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun s => radialArclength (G.flow.metric s) r)
      (intrinsicRadialVelocity (G.flow.metric t) hrotation hcomplete
        (radialArclength (G.flow.metric t) r)) t := by
  let g := G.flow.metric t
  have hint : (∫ a in (0 : ℝ)..r, rawAxisSpeedTimeDerivative G t a) =
      intrinsicRadialVelocity g hrotation hcomplete (radialArclength g r) := by
    calc
      _ = ∫ a in (0 : ℝ)..r,
          intrinsicRadialAcceleration g hrotation hcomplete (radialArclength g a) *
            axisRadialSpeed g a := intervalIntegral.integral_congr_Ioo_of_le hr
              (fun a ha => rawAxisSpeedTimeDerivative_eq_intrinsic G hrotation hcomplete ha.1)
      _ = _ := by
        have hh := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := r)
          (fun a _ => radialArclength_hasDerivAt g a)
          (axisRadialCoefficient_contDiff g).continuous.sqrt.continuousOn
          (intrinsicRadialAcceleration_contDiff g hrotation hcomplete).continuous
        simpa only [radialArclength_zero, intrinsicRadialVelocity, Function.comp_apply,
          axisRadialSpeed] using hh
  rw [← hint]
  exact raw_radialArclength_hasDerivAt_integral G ht hr

end PoincareMT.M35.Uniqueness
