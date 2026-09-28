import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLength












set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)




theorem m63ArcLength_abs_deriv_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    {t B : ℝ} (ht : t ∈ Set.Ioo a b)
    (hB : ∀ x ∈ Set.Icc alpha beta, m62Curvature F c t x ≤ B) :
    |deriv (fun s => m63ArcLength F c s alpha beta) t| ≤
      K2 * m63ArcLength F c t alpha beta +
        B * m63ArcTotalCurvature F c t alpha beta := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hK : Continuous (m62Curvature F c t) :=
    (curvature_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hKv : IntervalIntegrable
      (fun x => m62Curvature F c t x * curveSpeed F c t x)
      MeasureTheory.volume alpha beta := (hK.mul hV).intervalIntegrable alpha beta
  have hVint : IntervalIntegrable (curveSpeed F c t) MeasureTheory.volume alpha beta :=
    hV.intervalIntegrable alpha beta
  rw [(m63ArcLength_hasDerivAt F c hc hab ht).deriv, abs_neg]
  calc
    _ ≤ ∫ x in alpha..beta,
        |(m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
          curveSpeed F c t x| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in alpha..beta,
        K2 * curveSpeed F c t x +
          B * (m62Curvature F c t x * curveSpeed F c t x) := by
      apply intervalIntegral.integral_mono_on hab
        ((length_density_continuous F c hc ht).abs.intervalIntegrable _ _)
        ((hVint.const_mul K2).add (hKv.const_mul B))
      intro x hx
      have hunit := (unitTangent_norm F c hc hclosed x).le
      have hRic : |m62TangentRicci F c t x| ≤ K2 :=
        hBounds.ricci t hclosed (c x t)
          (spatialUnitTangent F c t x) (spatialUnitTangent F c t x) hunit hunit
      have hq : m62CurvatureSquared F c t x ≤ B * m62Curvature F c t x := by
        have h := mul_le_mul_of_nonneg_right (hB x hx) (curvature_nonneg F c t x)
        simpa only [← pow_two, curvature_sq] using h
      calc
        |(m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
            curveSpeed F c t x| =
          |m62CurvatureSquared F c t x + m62TangentRicci F c t x| *
            curveSpeed F c t x := by rw [abs_mul, abs_of_nonneg (speed_nonneg F c t x)]
        _ ≤ (m62CurvatureSquared F c t x + K2) * curveSpeed F c t x := by
          apply mul_le_mul_of_nonneg_right _ (speed_nonneg F c t x)
          calc
            _ ≤ |m62CurvatureSquared F c t x| + |m62TangentRicci F c t x| :=
              abs_add_le _ _
            _ ≤ m62CurvatureSquared F c t x + K2 := by
              rw [abs_of_nonneg (curvatureSquared_nonneg F c t x)]
              exact add_le_add le_rfl hRic
        _ ≤ (B * m62Curvature F c t x + K2) * curveSpeed F c t x :=
          mul_le_mul_of_nonneg_right (add_le_add hq le_rfl) (speed_nonneg F c t x)
        _ = K2 * curveSpeed F c t x +
            B * (m62Curvature F c t x * curveSpeed F c t x) := by ring
    _ = K2 * m63ArcLength F c t alpha beta +
        B * m63ArcTotalCurvature F c t alpha beta := by
      rw [intervalIntegral.integral_add (hVint.const_mul K2) (hKv.const_mul B),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rfl




theorem m63ArcLength_backward_loss (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (hK2 : 0 ≤ K2) {alpha beta : ℝ} (hab : alpha ≤ beta)
    {s T Lmax Thetamax : ℝ} (hs : a ≤ s) (hT : T ≤ b) (hsT : s < T)
    (_hTheta : 0 ≤ Thetamax)
    (hL : ∀ tau ∈ Set.Ioo s T, m63ArcLength F c tau alpha beta ≤ Lmax)
    (hTurning : ∀ tau ∈ Set.Ioo s T,
      m63ArcTotalCurvature F c tau alpha beta ≤ Thetamax)
    (hCurv : ∀ tau ∈ Set.Ioo s T, ∀ x ∈ Set.Icc alpha beta,
      m62CurvatureSquared F c tau x ≤ 2 / (tau - s))
    {t : ℝ} (ht : t ∈ Set.Icc s T) :
    m63ArcLength F c s alpha beta ≤
      m63ArcLength F c t alpha beta + K2 * Lmax * (t - s) +
        2 * Real.sqrt 2 * Thetamax * Real.sqrt (t - s) := by
  let L : ℝ → ℝ := fun tau => m63ArcLength F c tau alpha beta
  let G : ℝ → ℝ := fun tau => L tau + K2 * Lmax * (tau - s) +
    2 * Real.sqrt 2 * Thetamax * Real.sqrt (tau - s)
  have hLcont : ContinuousOn L (Set.Icc s T) :=
    (m63ArcLength_continuousOn F c hc alpha beta).mono (Set.Icc_subset_Icc hs hT)
  have hG : ContinuousOn G (Set.Icc s T) :=
    (hLcont.add (by fun_prop)).add (by fun_prop)
  have hd (tau : ℝ) (htau : tau ∈ Set.Ioo s T) :
      HasDerivAt G (deriv L tau + K2 * Lmax +
        Real.sqrt 2 * Thetamax / Real.sqrt (tau - s)) tau := by
    have htime : tau ∈ Set.Ioo a b := ⟨hs.trans_lt htau.1, htau.2.trans_le hT⟩
    have hroot : Real.sqrt (tau - s) ≠ 0 :=
      (Real.sqrt_pos.mpr (sub_pos.mpr htau.1)).ne'
    have hlength : HasDerivAt L (deriv L tau) tau :=
      (m63ArcLength_hasDerivAt F c hc hab htime).differentiableAt.hasDerivAt
    have hlinear := ((hasDerivAt_id tau).sub_const s).const_mul (K2 * Lmax)
    have hsqrt := (((hasDerivAt_id tau).sub_const s).sqrt
      (sub_pos.mpr htau.1).ne').const_mul (2 * Real.sqrt 2 * Thetamax)
    apply ((hlength.add hlinear).add hsqrt).congr_deriv
    simp only [id_eq]
    field_simp [hroot]
  have hnonneg (tau : ℝ) (htau : tau ∈ Set.Ioo s T) :
      0 ≤ deriv L tau + K2 * Lmax +
        Real.sqrt 2 * Thetamax / Real.sqrt (tau - s) := by
    have htime : tau ∈ Set.Ioo a b := ⟨hs.trans_lt htau.1, htau.2.trans_le hT⟩
    have hcap (x : ℝ) (hx : x ∈ Set.Icc alpha beta) :
        m62Curvature F c tau x ≤ Real.sqrt 2 / Real.sqrt (tau - s) := by
      exact (Real.sqrt_le_sqrt (hCurv tau htau x hx)).trans_eq
        (Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) (tau - s))
    have hupper : |deriv L tau| ≤ K2 * Lmax +
        Real.sqrt 2 * Thetamax / Real.sqrt (tau - s) := by
      calc
        _ ≤ K2 * L tau + (Real.sqrt 2 / Real.sqrt (tau - s)) *
            m63ArcTotalCurvature F c tau alpha beta :=
          m63ArcLength_abs_deriv_le F c hc hBounds hab htime hcap
        _ ≤ K2 * Lmax + (Real.sqrt 2 / Real.sqrt (tau - s)) * Thetamax :=
          add_le_add (mul_le_mul_of_nonneg_left (hL tau htau) hK2)
            (mul_le_mul_of_nonneg_left (hTurning tau htau)
              (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
        _ = _ := by ring
    linarith [neg_abs_le (deriv L tau)]
  have hmono : MonotoneOn G (Set.Icc s T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s T) hG
      (fun tau htau => (hd tau (by simpa only [interior_Icc] using htau)).hasDerivWithinAt)
      (fun tau htau => hnonneg tau (by simpa only [interior_Icc] using htau))
  have h := hmono (show s ∈ Set.Icc s T from ⟨le_rfl, hsT.le⟩) ht ht.1
  simpa only [G, L, sub_self, Real.sqrt_zero, mul_zero, add_zero] using h

end PoincareConjecture
