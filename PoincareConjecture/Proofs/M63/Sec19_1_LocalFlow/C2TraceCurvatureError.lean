import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalization
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureVectorEvolution

set_option autoImplicit false

open Set Bundle Manifold
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem curvatureVector_diffusionError_norm_le [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    (F.metric t).tangentNorm (c x t)
      (rampHorizontalCovariantDerivative (F.connection t) (fun r => c x r)
        (fun r => m62CurvatureVector F c r x) t - m63CurvatureJet F c 2 t x) ≤
      2 * m62Curvature F c t x ^ 3 + (K0 + 4 * K2) * m62Curvature F c t x +
        4 * K1 + 2 * m62Curvature F c t x *
          (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) := by
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let S := spatialUnitTangent F c t x
  let H := m62CurvatureVector F c t x
  let B := m63CurvatureJet F c 1 t x
  let Q := rampHorizontalCovariantDerivative D (fun r => c x r)
    (fun r => m62CurvatureVector F c r x) t - m63CurvatureJet F c 2 t x
  let A : ℝ → ℝ := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
  let k := m62Curvature F c t x
  let u := g.tangentNorm p B
  let N := g.tangentNorm p Q
  let C := 2 * k ^ 3 + (K0 + 4 * K2) * k + 4 * K1 + 2 * k * u
  have ht' := Ioo_subset_Icc_self ht
  have hv := speed_pos F c hc ht' x
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hB : g.tangentNorm p B = u := rfl
  have hN : g.tangentNorm p Q = N := rfl
  have hk : 0 ≤ k := curvature_nonneg F c t x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hu : 0 ≤ u := by simpa only [hn, hB] using norm_nonneg B
  have hN0 : 0 ≤ N := by simpa only [hn, hN] using norm_nonneg Q
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hRic : |D.ricci p S S| ≤ K2 := hBounds.ricci t ht' p S S hS.le hS.le
  have hA : |A x| ≤ K2 + k ^ 2 := by
    have hq := curvatureSquared_nonneg F c t x
    have hkq : k ^ 2 = m62CurvatureSquared F c t x := curvature_sq F c t x
    change |D.ricci p S S + m62CurvatureSquared F c t x| ≤ _
    rw [hkq]
    apply abs_le.mpr
    constructor
    · linarith only [(abs_le.mp hRic).1, hq]
    · linarith only [(abs_le.mp hRic).2]
  have hDA : |m62ArcDerivative F c t A x| ≤ K1 + 2 * K2 * k + 2 * k * u := by
    have hd := normalizationCoefficient_spatial_abs_bound F c hc hBounds ht x
    change |deriv A x| ≤ curveSpeed F c t x * (K1 + 2 * K2 * k + 2 * k * u) at hd
    have heq : curveSpeed F c t x * m62ArcDerivative F c t A x = deriv A x := by
      dsimp only [m62ArcDerivative]
      rw [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
    rw [← heq, abs_mul, abs_of_pos hv] at hd
    exact (mul_le_mul_iff_right₀ hv).mp hd
  have hHZ : |g.inner p H Q| ≤ k * N := by
    change |inner ℝ H Q| ≤ k * N
    simpa only [hn, hH, hN] using abs_real_inner_le_norm H Q
  have hSZ : |g.inner p S Q| ≤ N := by
    change |inner ℝ S Q| ≤ N
    simpa only [hn, hS, hN, one_mul] using abs_real_inner_le_norm S Q
  have hRm : |D.curvatureTensor p H S Q S| ≤ K0 * k * N := by
    have h := tensor_abs_le_of_unit_bound g D.riemannEvaluation
      (M04.isSmoothCovariantTensor_riemannEvaluation D) p
      (hBounds.riemann t ht' p) ![H, S, Q, S]
    simpa [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ,
      hH, hS, hN, mul_assoc] using h
  have hDer (w : Fin 3 → TangentSpace (𝓡 n) p) :
      |D.covariantTensorDerivative D.ricciEvaluation p w| ≤
        K1 * ∏ i, g.tangentNorm p (w i) :=
    tensor_abs_le_of_unit_bound g (D.covariantTensorDerivative D.ricciEvaluation)
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D
        (M04.isSmoothCovariantTensor_ricciEvaluation D)) p
      (hBounds.ricci_derivative t ht' p) w
  have hSSQ : |D.covariantTensorDerivative D.ricciEvaluation p ![S, S, Q]| ≤ K1 * N := by
    simpa [Fin.prod_univ_succ, hS, hN] using hDer ![S, S, Q]
  have hQSS : |D.covariantTensorDerivative D.ricciEvaluation p ![Q, S, S]| ≤ K1 * N := by
    simpa [Fin.prod_univ_succ, hS, hN] using hDer ![Q, S, S]
  have hlead : |2 * A x * g.inner p H Q| ≤ 2 * (K2 + k ^ 2) * (k * N) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hHZ
      (abs_nonneg _) (by positivity)
  have hnorm : |m62ArcDerivative F c t A x * g.inner p S Q| ≤
      (K1 + 2 * K2 * k + 2 * k * u) * N := by
    rw [abs_mul]
    exact mul_le_mul hDA hSZ (abs_nonneg _) (by positivity)
  have hevol := m63CurvatureVector_time_pair F c hc ht x Q
  have hpair : g.inner p Q Q = 2 * A x * g.inner p H Q +
      m62ArcDerivative F c t A x * g.inner p S Q + D.curvatureTensor p H S Q S -
        2 * D.covariantTensorDerivative D.ricciEvaluation p ![S, S, Q] +
          D.covariantTensorDerivative D.ricciEvaluation p ![Q, S, S] := by
    dsimp only at hevol
    change g.inner p
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62CurvatureVector F c r x) t) Q = _ at hevol
    calc
      g.inner p Q Q = g.inner p
          (rampHorizontalCovariantDerivative D (fun r => c x r)
            (fun r => m62CurvatureVector F c r x) t) Q -
          g.inner p (m63CurvatureJet F c 2 t x) Q := by
        change inner ℝ
          (rampHorizontalCovariantDerivative D (fun r => c x r)
            (fun r => m62CurvatureVector F c r x) t - m63CurvatureJet F c 2 t x) Q =
          inner ℝ _ Q - inner ℝ _ Q
        exact inner_sub_left _ _ _
      _ = _ := by linarith only [hevol]
  have habs : |g.inner p Q Q| ≤ C * N := by
    rw [hpair]
    apply abs_le.mpr
    dsimp only [C]
    constructor
    · nlinarith only [(abs_le.mp hlead).1, (abs_le.mp hnorm).1,
        (abs_le.mp hRm).1, (abs_le.mp hSSQ).2, (abs_le.mp hQSS).1]
    · nlinarith only [(abs_le.mp hlead).2, (abs_le.mp hnorm).2,
        (abs_le.mp hRm).2, (abs_le.mp hSSQ).1, (abs_le.mp hQSS).2]
  have hself : g.inner p Q Q = N ^ 2 := by
    change inner ℝ Q Q = N ^ 2
    simpa only [hn, hN] using real_inner_self_eq_norm_sq Q
  have hsquare : N ^ 2 ≤ C * N := by
    simpa only [hself, abs_of_nonneg (sq_nonneg N)] using habs
  change N ≤ C
  by_cases hz : N = 0
  · simpa only [hz] using hC
  · have hpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hz)
    nlinarith only [hsquare, hpos]

end PoincareConjecture.M63
