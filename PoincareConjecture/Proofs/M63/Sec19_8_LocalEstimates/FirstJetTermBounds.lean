import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.TangentRicciDerivatives
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds

set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63TangentRicci_arc_abs_bounds [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K : ℝ} (_hK : 0 ≤ K)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hSecond : ∀ v : Fin 4 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) (c x t) v| ≤ K) :
    let k := m62Curvature F c t x
    let q := m62CurvatureSquared F c t x
    let u := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x)
    |m62ArcDerivative F c t (m62TangentRicci F c t) x| ≤ K * (1 + 2 * k) ∧
      |m62ArcSecondDerivative F c t (m62TangentRicci F c t) x| ≤
        K * (1 + 5 * k + 2 * u + 2 * q) := by
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let S := spatialUnitTangent F c t x
  let H := m63CurvatureJet F c 0 t x
  let B := m63CurvatureJet F c 1 t x
  let k := m62Curvature F c t x
  let q := m62CurvatureSquared F c t x
  let u := g.tangentNorm p B
  have ht' := Ioo_subset_Icc_self ht
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hB : g.tangentNorm p B = u := rfl
  have hkq : k ^ 2 = q := curvature_sq F c t x
  have hRic (V W : TangentSpace (𝓡 n) p) :
      |D.ricci p V W| ≤ K * g.tangentNorm p V * g.tangentNorm p W := by
    have h := tensor_abs_le_of_unit_bound g D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) p
      (fun v hv => hBounds.ricci t ht' p (v 0) (v 1) (hv 0) (hv 1)) ![V, W]
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ, mul_assoc] using h
  have hT : IsSmoothCovariantTensor T :=
    M04.isSmoothCovariantTensor_covariantTensorDerivative D
      (M04.isSmoothCovariantTensor_ricciEvaluation D)
  have hDer (v : Fin 3 → TangentSpace (𝓡 n) p) :
      |T p v| ≤ K * ∏ i, g.tangentNorm p (v i) :=
    tensor_abs_le_of_unit_bound g T hT p (hBounds.ricci_derivative t ht' p) v
  have hSSS : |T p ![S, S, S]| ≤ K := by
    simpa [Fin.prod_univ_succ, hS] using hDer ![S, S, S]
  have hHSS : |T p ![H, S, S]| ≤ K * k := by
    simpa [Fin.prod_univ_succ, hH, hS] using hDer ![H, S, S]
  have hSHS : |T p ![S, H, S]| ≤ K * k := by
    simpa [Fin.prod_univ_succ, hH, hS] using hDer ![S, H, S]
  have hSSSS : |U p ![S, S, S, S]| ≤ K := by
    have h := tensor_abs_le_of_unit_bound g U
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D hT) p hSecond
      ![S, S, S, S]
    simpa [Fin.prod_univ_succ, hS] using h
  have hHS : |D.ricci p H S| ≤ K * k := by
    simpa only [hH, hS, mul_one] using hRic H S
  have hBS : |D.ricci p B S| ≤ K * u := by
    simpa only [hB, hS, mul_one] using hRic B S
  have hHH : |D.ricci p H H| ≤ K * q := by
    simpa only [hH, mul_assoc, ← pow_two, hkq] using hRic H H
  have heq := m63TangentRicci_arc_derivatives F c hc ht x
  change m62ArcDerivative F c t (m62TangentRicci F c t) x =
      T p ![S, S, S] + 2 * D.ricci p H S ∧
    m62ArcSecondDerivative F c t (m62TangentRicci F c t) x =
      U p ![S, S, S, S] + T p ![H, S, S] + 4 * T p ![S, H, S] +
        2 * D.ricci p B S + 2 * D.ricci p H H at heq
  change |m62ArcDerivative F c t (m62TangentRicci F c t) x| ≤ K * (1 + 2 * k) ∧
    |m62ArcSecondDerivative F c t (m62TangentRicci F c t) x| ≤
      K * (1 + 5 * k + 2 * u + 2 * q)
  rw [heq.1, heq.2]
  constructor
  · apply abs_le.mpr
    constructor
    · nlinarith only [(abs_le.mp hSSS).1, (abs_le.mp hHS).1]
    · nlinarith only [(abs_le.mp hSSS).2, (abs_le.mp hHS).2]
  · apply abs_le.mpr
    constructor
    · nlinarith only [(abs_le.mp hSSSS).1, (abs_le.mp hHSS).1,
        (abs_le.mp hSHS).1, (abs_le.mp hBS).1, (abs_le.mp hHH).1]
    · nlinarith only [(abs_le.mp hSSSS).2, (abs_le.mp hHSS).2,
        (abs_le.mp hSHS).2, (abs_le.mp hBS).2, (abs_le.mp hHH).2]

theorem m63FirstJet_ambient_abs_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K : ℝ} (_hK : 0 ≤ K)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hRiemann : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).riemannEvaluation (c x t) v| ≤ K)
    (hSecond : ∀ v : Fin 4 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) (c x t) v| ≤ K) :
    let D := F.connection t
    let Rm := D.riemannEvaluation
    let T := D.covariantTensorDerivative D.ricciEvaluation
    let U := D.covariantTensorDerivative T
    let J := D.covariantTensorDerivative Rm
    let S := spatialUnitTangent F c t x
    let H := m63CurvatureJet F c 0 t x
    let B := m63CurvatureJet F c 1 t x
    let q := m62CurvatureSquared F c t x
    let k := m62Curvature F c t x
    let beta := m63CurvatureJetSquared F c 1 t x
    let u := (F.metric t).tangentNorm (c x t) B
    |J (c x t) ![S, H, S, B, S] + Rm (c x t) ![B, S, B, S] +
      2 * Rm (c x t) ![H, S, B, H] - 2 * U (c x t) ![S, S, S, B] +
      U (c x t) ![S, B, S, S] - 3 * T (c x t) ![H, S, B] -
      3 * T (c x t) ![S, H, B] + 3 * T (c x t) ![B, S, H]| ≤
        K * beta + K * (2 * q + 10 * k + 3) * u := by
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let Rm := D.riemannEvaluation
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let J := D.covariantTensorDerivative Rm
  let S := spatialUnitTangent F c t x
  let H := m63CurvatureJet F c 0 t x
  let B := m63CurvatureJet F c 1 t x
  let k := m62Curvature F c t x
  let q := m62CurvatureSquared F c t x
  let beta := m63CurvatureJetSquared F c 1 t x
  let u := g.tangentNorm p B
  have ht' := Ioo_subset_Icc_self ht
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hB : g.tangentNorm p B = u := rfl
  have hkq : k ^ 2 = q := curvature_sq F c t x
  have hbeta : 0 ≤ beta := (g.toRiemannianMetric.toCore p).re_inner_nonneg B
  have hu : u ^ 2 = beta := by
    change (Real.sqrt beta) ^ 2 = beta
    exact Real.sq_sqrt hbeta
  have hRm : IsSmoothCovariantTensor Rm := M04.isSmoothCovariantTensor_riemannEvaluation D
  have hT : IsSmoothCovariantTensor T :=
    M04.isSmoothCovariantTensor_covariantTensorDerivative D
      (M04.isSmoothCovariantTensor_ricciEvaluation D)
  have hRmBound (v : Fin 4 → TangentSpace (𝓡 n) p) :
      |Rm p v| ≤ K * ∏ i, g.tangentNorm p (v i) :=
    tensor_abs_le_of_unit_bound g Rm hRm p (hBounds.riemann t ht' p) v
  have hTBound (v : Fin 3 → TangentSpace (𝓡 n) p) :
      |T p v| ≤ K * ∏ i, g.tangentNorm p (v i) :=
    tensor_abs_le_of_unit_bound g T hT p (hBounds.ricci_derivative t ht' p) v
  have hUBound (v : Fin 4 → TangentSpace (𝓡 n) p) :
      |U p v| ≤ K * ∏ i, g.tangentNorm p (v i) :=
    tensor_abs_le_of_unit_bound g U
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D hT) p hSecond v
  have hJ : |J p ![S, H, S, B, S]| ≤ K * k * u := by
    have h := tensor_abs_le_of_unit_bound g J
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D hRm) p hRiemann
      ![S, H, S, B, S]
    simpa [Fin.prod_univ_succ, hS, hH, hB, mul_assoc] using h
  have hRBB : |Rm p ![B, S, B, S]| ≤ K * beta := by
    simpa [Fin.prod_univ_succ, hS, hB, ← pow_two, hu] using hRmBound ![B, S, B, S]
  have hRHB : |Rm p ![H, S, B, H]| ≤ K * q * u := by
    have h := hRmBound ![H, S, B, H]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, hS, hH, hB, one_mul] at h
    calc
      _ ≤ K * (k * (u * k)) := h
      _ = K * q * u := by rw [← hkq]; ring
  have hUSSS : |U p ![S, S, S, B]| ≤ K * u := by
    simpa [Fin.prod_univ_succ, hS, hB] using hUBound ![S, S, S, B]
  have hUSBS : |U p ![S, B, S, S]| ≤ K * u := by
    simpa [Fin.prod_univ_succ, hS, hB] using hUBound ![S, B, S, S]
  have hTHSB : |T p ![H, S, B]| ≤ K * k * u := by
    simpa [Fin.prod_univ_succ, hS, hH, hB, mul_assoc] using hTBound ![H, S, B]
  have hTSHB : |T p ![S, H, B]| ≤ K * k * u := by
    simpa [Fin.prod_univ_succ, hS, hH, hB, mul_assoc] using hTBound ![S, H, B]
  have hTBSH : |T p ![B, S, H]| ≤ K * k * u := by
    simpa [Fin.prod_univ_succ, hS, hH, hB, mul_assoc, mul_comm, mul_left_comm]
      using hTBound ![B, S, H]
  change |J p ![S, H, S, B, S] + Rm p ![B, S, B, S] +
      2 * Rm p ![H, S, B, H] - 2 * U p ![S, S, S, B] +
      U p ![S, B, S, S] - 3 * T p ![H, S, B] -
      3 * T p ![S, H, B] + 3 * T p ![B, S, H]| ≤
    K * beta + K * (2 * q + 10 * k + 3) * u
  apply abs_le.mpr
  constructor
  · nlinarith only [(abs_le.mp hJ).1, (abs_le.mp hRBB).1,
      (abs_le.mp hRHB).1, (abs_le.mp hUSSS).2, (abs_le.mp hUSBS).1,
      (abs_le.mp hTHSB).2, (abs_le.mp hTSHB).2, (abs_le.mp hTBSH).1]
  · nlinarith only [(abs_le.mp hJ).2, (abs_le.mp hRBB).2,
      (abs_le.mp hRHB).2, (abs_le.mp hUSSS).1, (abs_le.mp hUSBS).2,
      (abs_le.mp hTHSB).1, (abs_le.mp hTSHB).1, (abs_le.mp hTBSH).2]

end PoincareConjecture
