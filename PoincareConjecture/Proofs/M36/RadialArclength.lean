import PoincareConjecture.Proofs.M36.AxisCoefficients
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M36

noncomputable def radialSpeed (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  Real.sqrt (axisRadialCoefficient g₀ r)

theorem radialSpeed_pos (g₀ : StandardInitialMetric) (r : ℝ) :
    0 < radialSpeed g₀ r := Real.sqrt_pos.mpr (axisRadialCoefficient_pos g₀ r)

theorem radialSpeed_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (radialSpeed g₀) :=
  (axisRadialCoefficient_contDiff g₀).sqrt fun r => (axisRadialCoefficient_pos g₀ r).ne'

noncomputable def radialArclength (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  ∫ t in 0..r, radialSpeed g₀ t

theorem radialArclength_zero (g₀ : StandardInitialMetric) :
    radialArclength g₀ 0 = 0 := intervalIntegral.integral_same

theorem radialArclength_hasDerivAt (g₀ : StandardInitialMetric) (r : ℝ) :
    HasDerivAt (radialArclength g₀) (radialSpeed g₀ r) r := by
  have hc := (radialSpeed_contDiff g₀).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem radialArclength_deriv (g₀ : StandardInitialMetric) :
    deriv (radialArclength g₀) = radialSpeed g₀ :=
  funext fun r => (radialArclength_hasDerivAt g₀ r).deriv

theorem radialArclength_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (radialArclength g₀) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (radialArclength_hasDerivAt g₀ r).differentiableAt, ?_⟩
  rw [radialArclength_deriv]
  exact radialSpeed_contDiff g₀

theorem radialArclength_strictMono (g₀ : StandardInitialMetric) :
    StrictMono (radialArclength g₀) :=
  strictMono_of_hasDerivAt_pos (radialArclength_hasDerivAt g₀) (radialSpeed_pos g₀)

theorem radialArclength_pos (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    0 < radialArclength g₀ r := by
  simpa only [radialArclength_zero] using radialArclength_strictMono g₀ hr

noncomputable def euclideanWarpRadius (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  r * Real.sqrt (axisTangentialCoefficient g₀ r)

theorem euclideanWarpRadius_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (euclideanWarpRadius g₀) :=
  contDiff_id.mul ((axisTangentialCoefficient_contDiff g₀).sqrt
    fun r => (axisTangentialCoefficient_pos g₀ r).ne')

theorem euclideanWarpRadius_zero (g₀ : StandardInitialMetric) :
    euclideanWarpRadius g₀ 0 = 0 := by simp [euclideanWarpRadius]

theorem euclideanWarpRadius_pos (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    0 < euclideanWarpRadius g₀ r :=
  mul_pos hr (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ r))

end PoincareConjecture.M36
