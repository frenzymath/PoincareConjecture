import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.C2Continuity
import PoincareConjecture.Proofs.M63.Mathlib.ClosedIntegralComparison
import PoincareConjecture.Proofs.M62.Lemma0_4_RegularizationError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)

theorem c2_estimates_of_interior (hc : M63C2ShrinkingCurveOn F c (Icc a T))
    (hT : a < T) {K0 K1 K2 : ℝ} (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hregularized_time : ∀ epsilon : ℝ, 0 < epsilon → ∀ t ∈ Ioo a T, ∀ x,
      DifferentiableAt ℝ (fun s => m62RegularizedCurvature F c epsilon s x) t)
    (hregularized_bound : ∀ epsilon : ℝ, 0 < epsilon → ∀ t ∈ Ioo a T, ∀ x,
      deriv (fun s => m62RegularizedCurvature F c epsilon s x) t ≤
        m62ArcSecondDerivative F c t (m62RegularizedCurvature F c epsilon t) x +
          m62Curvature F c t x ^ 3 +
          m62C1 K0 K1 K2 * (m62RegularizedCurvature F c epsilon t x + 1))
    (hlength_derivative : ∀ t ∈ Ioo a T,
      HasDerivAt (m62Length F c)
        (-(∫ x in (0 : ℝ)..curvePeriod,
          (m62CurvatureSquared F c t x + m62TangentRicci F c t x) * curveSpeed F c t x)) t)
    (hlength_energy : ∀ t ∈ Ioo a T,
      deriv (m62Length F c) t +
          (∫ x in (0 : ℝ)..curvePeriod, m62CurvatureSquared F c t x * curveSpeed F c t x) ≤
        K2 * m62Length F c t)
    (htotal_interior : ∀ s t : ℝ, s ∈ Ioo a T → t ∈ Ioo a T → s ≤ t →
      m62TotalCurvature F c t - m62TotalCurvature F c s ≤
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r) :
    M63C2CurveEstimates F c T K0 K1 K2 := by
  have hL := c2_length_continuous F c hc hT
  have hTheta := c2_totalCurvature_continuous F c hc hT
  have hEnergy := c2_curvatureEnergy_continuous F c hc hT
  have hEnergy_nonneg (t : ℝ) :
      0 ≤ ∫ x in (0 : ℝ)..curvePeriod, m62CurvatureSquared F c t x * curveSpeed F c t x :=
    intervalIntegral.integral_nonneg_of_forall (by unfold curvePeriod; positivity)
      (fun x => mul_nonneg (M62.curvatureSquared_nonneg F c t x) (M62.speed_nonneg F c t x))
  have hLderiv (t : ℝ) (ht : t ∈ Ioo a T) :
      HasDerivAt (m62Length F c) (deriv (m62Length F c) t) t :=
    (hlength_derivative t ht).differentiableAt.hasDerivAt
  have hLbound (t : ℝ) (ht : t ∈ Ioo a T) :
      deriv (m62Length F c) t ≤ K2 * m62Length F c t := by
    linarith [hlength_energy t ht, hEnergy_nonneg t]
  have htotal : ∀ s t : ℝ, s ∈ Icc a T → t ∈ Icc a T → s ≤ t →
      m62TotalCurvature F c t - m62TotalCurvature F c s ≤
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r := by
    intro s t hs ht hst
    exact intervalIntegral.sub_le_integral_of_interior_bound hT hTheta
      ((continuousOn_const.mul hTheta).add (continuousOn_const.mul hL))
      htotal_interior hs ht hst
  have hC : 0 ≤ m62C1 K0 K1 K2 := by
    unfold m62C1 m62C0
    positivity
  have hsum : ∀ s t : ℝ, s ∈ Icc a T → t ∈ Icc a T → s ≤ t →
      (m62TotalCurvature F c t + m62Length F c t) -
          (m62TotalCurvature F c s + m62Length F c s) ≤
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) *
          (m62TotalCurvature F c r + m62Length F c r) := by
    intro s t hs ht hst
    have hsub : Icc s t ⊆ Icc a T := Icc_subset_Icc hs.1 ht.2
    have hsub' : Ioo s t ⊆ Ioo a T := Ioo_subset_Ioo hs.1 ht.2
    have hLint := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst (hL.mono hsub)
      (fun r hr => (hLderiv r (hsub' hr)).hasDerivWithinAt)
      (continuousOn_const.mul (hL.mono hsub)).integrableOn_Icc
      (fun r hr => hLbound r (hsub' hr))
    change m62Length F c t - m62Length F c s ≤ ∫ r in s..t, K2 * m62Length F c r at hLint
    have hTforcing : ContinuousOn (fun r =>
        (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r) (Icc s t) :=
      (continuousOn_const.mul (hTheta.mono hsub)).add
        (continuousOn_const.mul (hL.mono hsub))
    have hLforcing : ContinuousOn (fun r => K2 * m62Length F c r) (Icc s t) :=
      continuousOn_const.mul (hL.mono hsub)
    have hint : (∫ r in s..t,
        (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r) +
        (∫ r in s..t, K2 * m62Length F c r) =
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) *
          (m62TotalCurvature F c r + m62Length F c r) := by
      rw [← intervalIntegral.integral_add
        (ContinuousOn.intervalIntegrable_of_Icc hst hTforcing)
        (ContinuousOn.intervalIntegrable_of_Icc hst hLforcing)]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      ring
    linarith [htotal s t hs ht hst]
  refine {
    length_continuous := hL
    total_curvature_continuous := hTheta
    regularized_positive := fun epsilon hepsilon t _ x => M62.regularized_pos F c hepsilon t x
    regularized_time := hregularized_time
    regularized_bound := hregularized_bound
    length_derivative := hlength_derivative
    total_curvature_integral := htotal
    length_exponential := fun s t hs ht hst =>
      Poincare.Parabolic.le_mul_exp_of_hasDerivAt_le_mul hL hLderiv hLbound hs ht hst
    total_exponential := fun s t hs ht hst =>
      Poincare.Parabolic.le_mul_exp_of_sub_le_integral_mul (add_nonneg hC hK2)
        (hTheta.add hL) hsum hs ht hst
    energy_integrable := c2_curvatureEnergy_integrable F c hc hT
    energy_bound := ?_ }
  exact Poincare.Parabolic.integral_le_mul_exp_of_energy_bound hT.le hK2 hL hEnergy hLderiv
    hlength_energy (fun t _ => hEnergy_nonneg t) (M62.length_nonneg F c T)

end PoincareConjecture.M63
