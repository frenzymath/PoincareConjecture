import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

noncomputable def distanceAverage (g : RiemannianMetric n M) (O : M)
    (μ : Measure M) : ℝ :=
  ∫ y, (g.edist O y).toReal + 2 ∂μ

theorem integrable_shiftedDistance_of_integrable_distance
    (g : RiemannianMetric n M) (O x : M) (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : Integrable (fun y ↦ (g.edist x y).toReal) μ) :
    Integrable (fun y ↦ (g.edist O y).toReal + 2) μ := by
  apply ((integrable_const ((g.edist O x).toReal)).add hμ |>.add
    (integrable_const (2 : ℝ))).mono'
    ((g.continuous_toReal_edist O).add continuous_const).aestronglyMeasurable
  filter_upwards [] with y
  change ‖(g.edist O y).toReal + 2‖ ≤
    (g.edist O x).toReal + (g.edist x y).toReal + 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith [g.toReal_edist_triangle O x y]

theorem abs_distanceAverage_sub_le_integral_distance
    (g : RiemannianMetric n M) (O x : M) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun y ↦ (g.edist x y).toReal) μ) :
    |g.distanceAverage O μ - ((g.edist O x).toReal + 2)| ≤
      ∫ y, (g.edist x y).toReal ∂μ := by
  have hint := g.integrable_shiftedDistance_of_integrable_distance O x μ hμ
  have hbound : ∀ᵐ y ∂μ,
      ‖((g.edist O y).toReal + 2) - ((g.edist O x).toReal + 2)‖ ≤
        (g.edist x y).toReal := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs, add_sub_add_right_eq_sub, abs_sub_comm]
    exact g.abs_toReal_edist_sub_le O x y
  have havg := norm_integral_le_of_norm_le hμ hbound
  rw [integral_sub hint (integrable_const _)] at havg
  simpa [distanceAverage, Real.norm_eq_abs] using havg

theorem integrable_shiftedDistance (g : RiemannianMetric n M) (O x : M)
    (μ : Measure M) [IsFiniteMeasure μ] {ε : ℝ}
    (hμ : ∀ᵐ y ∂μ, (g.edist x y).toReal ≤ ε) :
    Integrable (fun y ↦ (g.edist O y).toReal + 2) μ := by
  apply (integrable_const ((g.edist O x).toReal + ε + 2)).mono'
    ((g.continuous_toReal_edist O).add continuous_const).aestronglyMeasurable
  filter_upwards [hμ] with y hy
  change ‖(g.edist O y).toReal + 2‖ ≤ (g.edist O x).toReal + ε + 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htriangle := g.toReal_edist_triangle O x y
  linarith

theorem abs_distanceAverage_sub_le (g : RiemannianMetric n M) (O x : M)
    (μ : Measure M) [IsProbabilityMeasure μ] {ε : ℝ}
    (hμ : ∀ᵐ y ∂μ, (g.edist x y).toReal ≤ ε) :
    |g.distanceAverage O μ - ((g.edist O x).toReal + 2)| ≤ ε := by
  have hint := g.integrable_shiftedDistance O x μ hμ
  have hbound : ∀ᵐ y ∂μ,
      ‖((g.edist O y).toReal + 2) - ((g.edist O x).toReal + 2)‖ ≤ ε := by
    filter_upwards [hμ] with y hy
    rw [Real.norm_eq_abs, add_sub_add_right_eq_sub, abs_sub_comm]
    exact (g.abs_toReal_edist_sub_le O x y).trans hy
  have havg := norm_integral_le_of_norm_le_const hbound
  rw [integral_sub hint (integrable_const _)] at havg
  simpa [distanceAverage, Real.norm_eq_abs] using havg

theorem distanceAverage_bounds (g : RiemannianMetric n M) (O x : M)
    (μ : Measure M) [IsProbabilityMeasure μ] {ε : ℝ} (hε : ε ≤ 1)
    (hμ : ∀ᵐ y ∂μ, (g.edist x y).toReal ≤ ε) :
    (g.edist O x).toReal + 1 ≤ g.distanceAverage O μ ∧
      g.distanceAverage O μ ≤ 3 * ((g.edist O x).toReal + 1) := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp (g.abs_distanceAverage_sub_le O x μ hμ)
  have hnonneg := ENNReal.toReal_nonneg (a := g.edist O x)
  constructor <;> linarith

end PoincareConjecture.RiemannianMetric
