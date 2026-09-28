import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcCutoffTime
import PoincareConjecture.Proofs.M62.Cor0_3_RegularizedEvolution











set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem m63RegularizedDensity_time_derivative_bound (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    HasDerivAt
        (fun tau => m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x)
        ((m62SpatialEvolutionRhs F c t x / (2 * m62RegularizedCurvature F c ε t x) -
          m62RegularizedCurvature F c ε t x *
            (m62CurvatureSquared F c t x + m62TangentRicci F c t x)) *
          curveSpeed F c t x) t ∧
      deriv (fun tau => m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x) t ≤
        (m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
          (m62C1 K0 K1 K2 + K2) * m62RegularizedCurvature F c ε t x +
          m62C1 K0 K1 K2) * curveSpeed F c t x := by
  have hR := regularized_hasDerivAt_time F c hε
    (hasDerivAt_curvatureSquared F c hc ht x)
  have hD : HasDerivAt
      (fun tau => m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x)
      ((m62SpatialEvolutionRhs F c t x / (2 * m62RegularizedCurvature F c ε t x) -
        m62RegularizedCurvature F c ε t x *
          (m62CurvatureSquared F c t x + m62TangentRicci F c t x)) *
        curveSpeed F c t x) t := by
    apply (hR.mul (hasDerivAt_speed F c hc ht x)).congr_deriv
    ring
  refine ⟨hD, ?_⟩
  have hb := regularized_deriv_le F c hc h0 h1 h2 hBounds hε ht x
  rw [hR.deriv] at hb
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hunit := (unitTangent_norm F c hc hclosed x).le
  have hRic : -K2 ≤ m62TangentRicci F c t x :=
    (abs_le.mp (hBounds.ricci t hclosed (c x t)
      (spatialUnitTangent F c t x) (spatialUnitTangent F c t x) hunit hunit)).1
  have hRicmul := mul_le_mul_of_nonneg_left hRic (regularized_pos F c hε t x).le
  have hcubic : m62Curvature F c t x ^ 3 ≤
      m62RegularizedCurvature F c ε t x * m62CurvatureSquared F c t x := by
    calc
      _ = m62Curvature F c t x * m62Curvature F c t x ^ 2 := by ring
      _ ≤ m62RegularizedCurvature F c ε t x * m62Curvature F c t x ^ 2 :=
        mul_le_mul_of_nonneg_right (curvature_le_regularized F c ε t x) (sq_nonneg _)
      _ = _ := by rw [curvature_sq F c t x]
  have hscalar :
      m62SpatialEvolutionRhs F c t x / (2 * m62RegularizedCurvature F c ε t x) -
        m62RegularizedCurvature F c ε t x *
          (m62CurvatureSquared F c t x + m62TangentRicci F c t x) ≤
      m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
        (m62C1 K0 K1 K2 + K2) * m62RegularizedCurvature F c ε t x +
        m62C1 K0 K1 K2 := by
    nlinarith only [hb, hcubic, hRicmul]
  rw [hD.deriv]
  exact mul_le_mul_of_nonneg_right hscalar (speed_nonneg F c t x)



theorem m63ArcCutoff_regularizedDensity_deriv_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta x0 x : ℝ} (hab : alpha ≤ beta)
    (hx0 : x0 ∈ Set.Icc alpha beta) (hx : x ∈ Set.Icc alpha beta)
    {t r B P1 ε : ℝ} (ht : t ∈ Set.Ioo a b) (hε : 0 < ε) (hr : 0 < r)
    (hB : 0 ≤ B) (hcap : ∀ y ∈ Set.Icc alpha beta, m62Curvature F c t y ≤ B)
    (psi : ℝ → ℝ) (hP1 : 0 ≤ P1) (hpsi : ContDiff ℝ 2 psi)
    (hpsiNonneg : 0 ≤ psi (m63ArcLength F c t x0 x / r))
    (hpsiBound : |deriv psi (m63ArcLength F c t x0 x / r)| ≤ P1) :
    DifferentiableAt ℝ
        (fun tau => psi (m63ArcLength F c tau x0 x / r) *
          m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x) t ∧
      deriv (fun tau => psi (m63ArcLength F c tau x0 x / r) *
          m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x) t ≤
        ((P1 / r) * (K2 * m63ArcLength F c t alpha beta +
            B * m63ArcTotalCurvature F c t alpha beta) *
            m62RegularizedCurvature F c ε t x +
          psi (m63ArcLength F c t x0 x / r) *
            m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
          (m62C1 K0 K1 K2 + K2) * psi (m63ArcLength F c t x0 x / r) *
            m62RegularizedCurvature F c ε t x +
          m62C1 K0 K1 K2 * psi (m63ArcLength F c t x0 x / r)) *
          curveSpeed F c t x := by
  let phi := fun tau => psi (m63ArcLength F c tau x0 x / r)
  let density := fun tau => m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x
  let C := (P1 / r) * (K2 * m63ArcLength F c t alpha beta +
    B * m63ArcTotalCurvature F c t alpha beta)
  have hcut := m63ArcCutoff_time_derivative_bound F c hc hBounds h2 hab hx0 hx
    ht hr hB hcap psi hP1 ((hpsi.differentiable (by norm_num)) _) hpsiBound
  have hd := m63RegularizedDensity_time_derivative_bound F c hc h0 h1 h2 hBounds hε ht x
  have hphi : HasDerivAt phi (deriv phi t) t := hcut.1.differentiableAt.hasDerivAt
  have hdensity : HasDerivAt density (deriv density t) t := hd.1.differentiableAt.hasDerivAt
  have hprod : HasDerivAt
      (fun tau => psi (m63ArcLength F c tau x0 x / r) *
        m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x)
      (deriv phi t * density t + phi t * deriv density t) t := by
    simpa only [phi, density, mul_assoc] using hphi.fun_mul hdensity
  refine ⟨hprod.differentiableAt, ?_⟩
  rw [hprod.deriv]
  have hphiBound : deriv phi t ≤ C := (le_abs_self _).trans hcut.2
  have hdensityNonneg : 0 ≤ density t :=
    mul_nonneg (regularized_pos F c hε t x).le (speed_nonneg F c t x)
  calc
    _ ≤ C * density t + phi t *
        ((m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
          (m62C1 K0 K1 K2 + K2) * m62RegularizedCurvature F c ε t x +
          m62C1 K0 K1 K2) * curveSpeed F c t x) :=
      add_le_add (mul_le_mul_of_nonneg_right hphiBound hdensityNonneg)
        (mul_le_mul_of_nonneg_left hd.2 hpsiNonneg)
    _ = _ := by dsimp only [C, phi, density]; ring

end PoincareConjecture
