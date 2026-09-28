import PoincareConjecture.Statements.M62CurveEvolution
import PoincareConjecture.Proofs.M62.Mathlib.IntegralApproximation
import PoincareConjecture.Proofs.M62.Mathlib.ForwardIntegralBound

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem total_curvature_integral_of_regularized_bound {K0 K1 K2 : ℝ}
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hL : ContinuousOn (m62Length F c) (Set.Icc a b))
    (hT : ContinuousOn (m62TotalCurvature F c) (Set.Icc a b))
    (hR : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (m62RegularizedTotalCurvature F c ε) (Set.Icc a b))
    (hdiff : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a b,
      DifferentiableAt ℝ (m62RegularizedTotalCurvature F c ε) t)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a b,
      deriv (m62RegularizedTotalCurvature F c ε) t ≤
        (m62C1 K0 K1 K2 + K2) * m62RegularizedTotalCurvature F c ε t +
          m62C1 K0 K1 K2 * m62Length F c t)
    (herror : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc a b,
      0 ≤ m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ∧
        m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ≤
          ε * m62Length F c t)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    m62TotalCurvature F c t - m62TotalCurvature F c s ≤
      ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
        m62C1 K0 K1 K2 * m62Length F c r := by
  have hA : 0 ≤ m62C1 K0 K1 K2 + K2 := by
    unfold m62C1 m62C0
    positivity
  refine intervalIntegral.sub_le_integral_of_nonneg_approximation
    hA hT hL hR herror ?_ hs ht hst
  intro ε hε s t hs ht hst
  have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 ht.2
  have hinterior : Set.Ioo s t ⊆ Set.Ioo a b :=
    Set.Ioo_subset_Ioo hs.1 ht.2
  have hRc := (hR ε hε).mono hsub
  have hupper : ContinuousOn (fun r ↦
      (m62C1 K0 K1 K2 + K2) * m62RegularizedTotalCurvature F c ε r +
        m62C1 K0 K1 K2 * m62Length F c r) (Set.Icc s t) :=
    (continuousOn_const.mul hRc).add (continuousOn_const.mul (hL.mono hsub))
  exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst hRc
    (fun r hr ↦ (hdiff ε hε r (hinterior hr)).hasDerivAt.hasDerivWithinAt)
    hupper.integrableOn_Icc (fun r hr ↦ hbound ε hε r (hinterior hr))

theorem total_curvature_forward_of_integral_bound {K0 K1 K2 : ℝ}
    (hL : ContinuousOn (m62Length F c) (Set.Icc a b))
    (hT : ContinuousOn (m62TotalCurvature F c) (Set.Icc a b))
    (hbound : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
      m62TotalCurvature F c t - m62TotalCurvature F c s ≤
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r)
    {t : ℝ} (ht : t ∈ Set.Ico a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → t + h ∈ Set.Icc a b →
      (m62TotalCurvature F c (t + h) - m62TotalCurvature F c t) / h ≤
        (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c t +
          m62C1 K0 K1 K2 * m62Length F c t + ε := by
  exact intervalIntegral.forward_quotient_le_of_sub_le_integral
    ((continuousOn_const.mul hT).add (continuousOn_const.mul hL)) hbound ht hε

end PoincareConjecture.M62
