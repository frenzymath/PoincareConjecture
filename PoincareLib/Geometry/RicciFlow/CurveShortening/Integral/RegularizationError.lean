import PoincareLib.Geometry.RicciFlow.CurveShortening.Regularization.Basic
import PoincareLib.Geometry.RicciFlow.CurveShortening.Evolution.Speed

/-!
# Error of regularized total curvature

The 2015 correction, Lemma 0.4, pp. 7-8, passes to the limit in regularized
total curvature. The quantitative bound below justifies that passage once
the differential inequality has been integrated in time. Integrability is
explicit; no totalized integral is used to bypass it.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

/-- The actual parameter length is nonnegative; correction Lemma 0.4, p. 7. -/
theorem length_nonneg (t : ℝ) : 0 ≤ m62Length F c t := by
  exact intervalIntegral.integral_nonneg_of_forall
    (by unfold curvePeriod; positivity) (speed_nonneg F c t)

/-- Integrating the pointwise error gives the limiting estimate; correction pp. 7-8. -/
theorem regularization_error {ε t : ℝ} (hε : 0 ≤ ε)
    (hv : IntervalIntegrable (curveSpeed F c t) MeasureTheory.volume 0 curvePeriod)
    (hk : IntervalIntegrable (fun x ↦ m62Curvature F c t x * curveSpeed F c t x)
      MeasureTheory.volume 0 curvePeriod)
    (hh : IntervalIntegrable
      (fun x ↦ m62RegularizedCurvature F c ε t x * curveSpeed F c t x)
      MeasureTheory.volume 0 curvePeriod) :
    0 ≤ m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ∧
      m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ≤
        ε * m62Length F c t := by
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hdiff : m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t =
      ∫ x in (0 : ℝ)..curvePeriod,
        m62RegularizedCurvature F c ε t x * curveSpeed F c t x -
          m62Curvature F c t x * curveSpeed F c t x :=
    (intervalIntegral.integral_sub hh hk).symm
  rw [hdiff]
  constructor
  · apply intervalIntegral.integral_nonneg_of_forall hperiod
    intro x
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right
      (curvature_le_regularized F c ε t x) (speed_nonneg F c t x))
  · calc
      _ ≤ ∫ x in (0 : ℝ)..curvePeriod, ε * curveSpeed F c t x := by
        apply intervalIntegral.integral_mono_on hperiod (hh.sub hk) (hv.const_mul ε)
        intro x _
        rw [← sub_mul]
        exact mul_le_mul_of_nonneg_right
          (regularized_sub_curvature_le F c hε t x) (speed_nonneg F c t x)
      _ = ε * m62Length F c t := intervalIntegral.integral_const_mul _ _

end PoincareMT.M62
