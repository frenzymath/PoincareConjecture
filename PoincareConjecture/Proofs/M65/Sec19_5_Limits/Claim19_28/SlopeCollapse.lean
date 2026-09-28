import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SlopeIntegral
import PoincareConjecture.Proofs.M65.Mathlib.Claim19_28.WeightedOscillation
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m65Slope_sq_le_circumference (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t ell K : ℝ} (ht : t ∈ Icc a b) (hell : 0 < ell)
    (hL : ell ≤ m62Length P.flow c t) (hK : 0 ≤ K)
    (hramp : ∀ x, 0 ≤ m62Slope P c t x)
    (hcurv : ∀ x, m62Curvature P.flow c t x ≤ K)
    (L : M63PositiveDegreeLift P (fun x => c x t)) (hdegree : L.degree = 1)
    (x : ℝ) :
    m62Slope P c t x ^ 2 ≤ (circumference / ell) ^ 2 + 2 * K * circumference := by
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hv : Continuous (curveSpeed P.flow c t) :=
    (M62.speed_continuousOn P.flow c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hmass := m65Slope_integral_period_eq_circumference P c hc ht L hdegree x
  have hlength : (∫ y in x..x + curvePeriod, curveSpeed P.flow c t y) =
      m62Length P.flow c t := by
    simpa only [zero_add, m62Length] using
      (M62.speed_periodic P.flow c hc ht).intervalIntegral_add_eq x 0
  have hderiv : ∀ y ∈ Icc x (x + curvePeriod),
      |deriv (m62Slope P c t) y| ≤ K * curveSpeed P.flow c t y := by
    intro y _
    exact (m65Slope_deriv_abs_le P c hc ht y).trans
      (by simpa only [mul_comm K] using
        mul_le_mul_of_nonneg_left (hcurv y) (M62.speed_nonneg P.flow c t y))
  have hbound := M65.sq_le_weighted_average_sq_add_mass
    (show x ≤ x + curvePeriod by linarith)
    (fun y => (m65Slope_hasDerivAt P c hc ht y).differentiableAt) hv hK
    (fun y _ => hramp y) (fun y _ => M62.speed_nonneg P.flow c t y)
    hderiv (by rw [hlength]; exact hell.trans_le hL)
    (show x ∈ Icc x (x + curvePeriod) by exact ⟨le_rfl, by linarith⟩)
  rw [hmass, hlength] at hbound
  have hratio : circumference / m62Length P.flow c t ≤ circumference / ell :=
    div_le_div_of_nonneg_left P.circle.positive.le hell hL
  have hsquare := pow_le_pow_left₀
    (div_nonneg P.circle.positive.le (hell.le.trans hL)) hratio 2
  exact hbound.trans (add_le_add hsquare le_rfl)

end PoincareConjecture
