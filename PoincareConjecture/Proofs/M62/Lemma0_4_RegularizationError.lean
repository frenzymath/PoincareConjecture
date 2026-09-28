import PoincareConjecture.Proofs.M62.Cor0_3_Regularization
import PoincareConjecture.Proofs.M62.Lemma0_1_Speed

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem length_nonneg (t : ℝ) : 0 ≤ m62Length F c t := by
  exact intervalIntegral.integral_nonneg_of_forall
    (by unfold curvePeriod; positivity) (speed_nonneg F c t)

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

end PoincareConjecture.M62
