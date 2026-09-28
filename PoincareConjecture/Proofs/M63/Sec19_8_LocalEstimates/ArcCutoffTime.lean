import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLoss










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem m63SignedArcLength_hasDerivAt (hc : M62ShrinkingCurve F c)
    (x0 x : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun tau => m63ArcLength F c tau x0 x)
      (-(∫ y in x0..x,
        (m62CurvatureSquared F c t y + m62TangentRicci F c t y) *
          curveSpeed F c t y)) t := by
  rcases le_total x0 x with horder | horder
  · exact m63ArcLength_hasDerivAt F c hc horder ht
  · have heq : (fun tau => m63ArcLength F c tau x0 x) =
        (fun tau => -m63ArcLength F c tau x x0) := by
      funext tau
      exact intervalIntegral.integral_symm x x0
    rw [heq]
    apply ((m63ArcLength_hasDerivAt F c hc horder ht).neg).congr_deriv
    rw [intervalIntegral.integral_symm x x0]




theorem m63ArcCutoff_time_derivative_bound (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (hK2 : 0 ≤ K2) {alpha beta x0 x : ℝ} (_hab : alpha ≤ beta)
    (hx0 : x0 ∈ Set.Icc alpha beta) (hx : x ∈ Set.Icc alpha beta)
    {t r B P1 : ℝ} (ht : t ∈ Set.Ioo a b) (hr : 0 < r) (hB : 0 ≤ B)
    (hcap : ∀ y ∈ Set.Icc alpha beta, m62Curvature F c t y ≤ B)
    (psi : ℝ → ℝ) (hP1 : 0 ≤ P1)
    (hpsi : DifferentiableAt ℝ psi (m63ArcLength F c t x0 x / r))
    (hpsiBound : |deriv psi (m63ArcLength F c t x0 x / r)| ≤ P1) :
    HasDerivAt (fun tau => psi (m63ArcLength F c tau x0 x / r))
      ((deriv psi (m63ArcLength F c t x0 x / r) / r) *
        (-(∫ y in x0..x,
          (m62CurvatureSquared F c t y + m62TangentRicci F c t y) *
            curveSpeed F c t y))) t ∧
      |deriv (fun tau => psi (m63ArcLength F c tau x0 x / r)) t| ≤
        (P1 / r) * (K2 * m63ArcLength F c t alpha beta +
          B * m63ArcTotalCurvature F c t alpha beta) := by
  let d : ℝ := -(∫ y in x0..x,
    (m62CurvatureSquared F c t y + m62TangentRicci F c t y) * curveSpeed F c t y)
  have hd : HasDerivAt (fun tau => m63ArcLength F c tau x0 x) d t :=
    m63SignedArcLength_hasDerivAt F c hc x0 x ht
  have hchain : HasDerivAt (fun tau => psi (m63ArcLength F c tau x0 x / r))
      ((deriv psi (m63ArcLength F c t x0 x / r) / r) * d) t := by
    apply (hpsi.hasDerivAt.comp t (hd.div_const r)).congr_deriv
    ring
  refine ⟨hchain, ?_⟩
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hK : Continuous (m62Curvature F c t) :=
    (curvature_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hordered (l u : ℝ) (hlu : l ≤ u)
      (hl : l ∈ Set.Icc alpha beta) (hu : u ∈ Set.Icc alpha beta) :
      |deriv (fun tau => m63ArcLength F c tau l u) t| ≤
        K2 * m63ArcLength F c t alpha beta +
          B * m63ArcTotalCurvature F c t alpha beta := by
    have hsmall : ∀ y ∈ Set.Icc l u, m62Curvature F c t y ≤ B :=
      fun y hy => hcap y ⟨hl.1.trans hy.1, hy.2.trans hu.2⟩
    have hL : m63ArcLength F c t l u ≤ m63ArcLength F c t alpha beta :=
      intervalIntegral.integral_mono_interval hl.1 hlu hu.2
        (Filter.Eventually.of_forall (speed_nonneg F c t)) (hV.intervalIntegrable _ _)
    have hT : m63ArcTotalCurvature F c t l u ≤
        m63ArcTotalCurvature F c t alpha beta :=
      intervalIntegral.integral_mono_interval hl.1 hlu hu.2
        (Filter.Eventually.of_forall fun y =>
          mul_nonneg (curvature_nonneg F c t y) (speed_nonneg F c t y))
        ((hK.mul hV).intervalIntegrable _ _)
    exact (m63ArcLength_abs_deriv_le F c hc hBounds hlu ht hsmall).trans
      (add_le_add (mul_le_mul_of_nonneg_left hL hK2) (mul_le_mul_of_nonneg_left hT hB))
  have hdBound : |d| ≤ K2 * m63ArcLength F c t alpha beta +
      B * m63ArcTotalCurvature F c t alpha beta := by
    rw [← hd.deriv]
    rcases le_total x0 x with horder | horder
    · exact hordered x0 x horder hx0 hx
    · have heq : (fun tau => m63ArcLength F c tau x0 x) =
          (fun tau => -m63ArcLength F c tau x x0) := by
        funext tau
        exact intervalIntegral.integral_symm x x0
      rw [heq, deriv.fun_neg, abs_neg]
      exact hordered x x0 horder hx hx0
  rw [hchain.deriv, abs_mul, abs_div, abs_of_pos hr]
  exact mul_le_mul (div_le_div_of_nonneg_right hpsiBound hr.le) hdBound
    (abs_nonneg d) (div_nonneg hP1 hr.le)

end PoincareConjecture
