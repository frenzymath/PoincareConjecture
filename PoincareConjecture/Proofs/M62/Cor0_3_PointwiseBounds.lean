import PoincareConjecture.Proofs.M62.Mathlib.MultilinearUnitBound
import PoincareConjecture.Proofs.M62.Lemma0_2_CurveLaws
import PoincareConjecture.Proofs.M62.Cor0_3_AmbientBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem tensor_abs_le_of_unit_bound
    (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (hT : IsSmoothCovariantTensor T)
    (p : M) {K : ℝ}
    (hbound : ∀ v : Fin k → TangentSpace (𝓡 n) p,
      (∀ i, g.tangentNorm p (v i) ≤ 1) → |T p v| ≤ K)
    (v : Fin k → TangentSpace (𝓡 n) p) :
    |T p v| ≤ K * ∏ i, g.tangentNorm p (v i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hT.1 p
  have hn (w : TangentSpace (𝓡 n) p) : ‖w‖ = g.tangentNorm p w := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have h := A.norm_le_mul_prod_of_unit_bound (K := K) (fun w hw => by
    simpa only [← hA, Real.norm_eq_abs] using
      hbound w (fun i => by simpa only [← hn] using hw i)) v
  simpa only [← hA, Real.norm_eq_abs, hn] using h

set_option maxHeartbeats 800000 in

theorem spatialEvolutionRhs_add_ricci_sq_le
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    m62SpatialEvolutionRhs F c t x +
      2 * ((F.connection t).ricci (c x t) (spatialUnitTangent F c t x)
        (m62CurvatureVector F c t x)) ^ 2 ≤
      m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
        2 * (F.metric t).inner (c x t) (m62SpatialNormalDerivative F c t x)
          (m62SpatialNormalDerivative F c t x) +
        2 * (m62CurvatureSquared F c t x) ^ 2 +
        m62C0 K0 K1 K2 * (m62CurvatureSquared F c t x + m62Curvature F c t x) := by
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let H := m62CurvatureVector F c t x
  let S := spatialUnitTangent F c t x
  let q := m62CurvatureSquared F c t x
  let k := m62Curvature F c t x
  have ht' := Set.Ioo_subset_Icc_self ht
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hk : 0 ≤ k := curvature_nonneg F c t x
  have hq : 0 ≤ q := curvatureSquared_nonneg F c t x
  have hkq : k ^ 2 = q := curvature_sq F c t x
  have hRic (V W : TangentSpace (𝓡 n) p) :
      |D.ricci p V W| ≤ K2 * g.tangentNorm p V * g.tangentNorm p W := by
    have h := tensor_abs_le_of_unit_bound g D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) p (K := K2)
      (fun v hv => hBounds.ricci t ht' p (v 0) (v 1) (hv 0) (hv 1)) ![V, W]
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ, mul_assoc] using h
  have hHH : |D.ricci p H H| ≤ K2 * q := by
    simpa only [hH, mul_assoc, ← pow_two, hkq] using hRic H H
  have hSS : |D.ricci p S S| ≤ K2 := by
    simpa only [hS, mul_one] using hRic S S
  have hSH : |D.ricci p S H| ≤ K2 * k := by
    simpa only [hS, hH, mul_one] using hRic S H
  have hRm : |D.curvatureTensor p H S H S| ≤ K0 * q := by
    have h := tensor_abs_le_of_unit_bound g D.riemannEvaluation
      (M04.isSmoothCovariantTensor_riemannEvaluation D) p (K := K0)
      (hBounds.riemann t ht' p) ![H, S, H, S]
    simpa [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ, hH, hS,
      ← pow_two, hkq] using h
  have hDer (v : Fin 3 → TangentSpace (𝓡 n) p) :
      |D.covariantTensorDerivative D.ricciEvaluation p v| ≤
        K1 * ∏ i, g.tangentNorm p (v i) :=
    tensor_abs_le_of_unit_bound g (D.covariantTensorDerivative D.ricciEvaluation)
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D
        (M04.isSmoothCovariantTensor_ricciEvaluation D)) p
      (hBounds.ricci_derivative t ht' p) v
  have hHSS : |D.covariantTensorDerivative D.ricciEvaluation p ![H, S, S]| ≤
      K1 * k := by simpa [Fin.prod_univ_succ, hH, hS] using hDer ![H, S, S]
  have hSSH : |D.covariantTensorDerivative D.ricciEvaluation p ![S, S, H]| ≤
      K1 * k := by simpa [Fin.prod_univ_succ, hH, hS] using hDer ![S, S, H]
  have hSHsq : (D.ricci p S H) ^ 2 ≤ K2 ^ 2 * q := by
    calc
      _ = |D.ricci p S H| ^ 2 := (sq_abs _).symm
      _ ≤ (K2 * k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hSH 2
      _ = _ := by rw [mul_pow, hkq]
  have hSSq : 4 * q * D.ricci p S S ≤ 4 * q * K2 :=
    mul_le_mul_of_nonneg_left (abs_le.mp hSS).2 (by positivity)
  have hslack : 0 ≤ (2 * K0 + 6 * K2 + 2 * K2 ^ 2) * k + 6 * K1 * q := by
    positivity
  dsimp only [m62SpatialEvolutionRhs, m62C0]
  change _ + 2 * (D.ricci p S H) ^ 2 ≤ _
  nlinarith only [(abs_le.mp hHH).1, (abs_le.mp hRm).2,
    (abs_le.mp hHSS).2, (abs_le.mp hSSH).1, hSHsq, hSSq, hslack]

theorem spatial_squared_bound [T2Space M]
    (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    deriv (fun s => m62CurvatureSquared F c s x) t ≤
      m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
        2 * (F.metric t).inner (c x t) (m62SpatialNormalDerivative F c t x)
          (m62SpatialNormalDerivative F c t x) +
        2 * (m62CurvatureSquared F c t x) ^ 2 +
        m62C0 K0 K1 K2 * (m62CurvatureSquared F c t x + m62Curvature F c t x) := by
  rw [(hasDerivAt_curvatureSquared F c hc ht x).deriv]
  exact (le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))).trans
    (spatialEvolutionRhs_add_ricci_sq_le F c hc h0 h1 h2 hBounds ht x)

theorem SpacetimeData.curvature_squared_bound [T2Space M]
    {F : RicciFlow n M (Set.Icc a b)} (G : SpacetimeData F)
    (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    M62SpacetimeEstimate G c K0 K1 K2 := by
  intro t x
  dsimp only
  rw [(hasDerivAt_curvatureSquared F c hc t.property x).deriv, G.normal_norm c hc t x]
  have h := spatialEvolutionRhs_add_ricci_sq_le F c hc h0 h1 h2 hBounds t.property x
  linarith

end PoincareConjecture.M62
