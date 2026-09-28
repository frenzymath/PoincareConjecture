import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetEvolution
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetTermBounds

set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63FirstJetSquared_dissipation [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hcurv : m62CurvatureSquared F c t x ≤ R)
    (hRiemann : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).riemannEvaluation (c x t) v| ≤ K)
    (hSecond : ∀ v : Fin 4 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) (c x t) v| ≤ K) :
    let C := 14 * R + 10 * K + 1 + 4 * R ^ 3 + 2 * R * K * (7 * R + 6) +
      (K * (46 * R + 32)) ^ 2
    deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x ≤
      -m63CurvatureJetSquared F c 2 t x + C * m63CurvatureJetSquared F c 1 t x + C := by
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
  let V := m63CurvatureJet F c 2 t x
  let k := m62Curvature F c t x
  let q := m62CurvatureSquared F c t x
  let beta := m63CurvatureJetSquared F c 1 t x
  let chi := m63CurvatureJetSquared F c 2 t x
  let u := g.tangentNorm p B
  let w := g.tangentNorm p V
  let N := g.inner p H B
  let r := m62TangentRicci F c t
  let E := J p ![S, H, S, B, S] + Rm p ![B, S, B, S] +
    2 * Rm p ![H, S, B, H] - 2 * U p ![S, S, S, B] +
    U p ![S, B, S, S] - 3 * T p ![H, S, B] -
    3 * T p ![S, H, B] + 3 * T p ![B, S, H]
  let L := deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
    m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x
  let C := 14 * R + 10 * K + 1 + 4 * R ^ 3 + 2 * R * K * (7 * R + 6) +
    (K * (46 * R + 32)) ^ 2
  change L ≤ -chi + C * beta + C
  have ht' := Ioo_subset_Icc_self ht
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hB : g.tangentNorm p B = u := rfl
  have hV : g.tangentNorm p V = w := rfl
  have hk : 0 ≤ k := curvature_nonneg F c t x
  have hq : 0 ≤ q := curvatureSquared_nonneg F c t x
  have hbeta : 0 ≤ beta := (g.toRiemannianMetric.toCore p).re_inner_nonneg B
  have hchi : 0 ≤ chi := (g.toRiemannianMetric.toCore p).re_inner_nonneg V
  have hun : 0 ≤ u := Real.sqrt_nonneg _
  have hkq : k ^ 2 = q := curvature_sq F c t x
  have hu : u ^ 2 = beta := Real.sq_sqrt hbeta
  have hw : w ^ 2 = chi := Real.sq_sqrt hchi
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hN : |N| ≤ k * u := by
    change |inner ℝ H B| ≤ k * u
    simpa only [hn, hH, hB] using abs_real_inner_le_norm H B
  have hNsq : N ^ 2 ≤ q * beta := by
    change (inner ℝ H B) ^ 2 ≤ inner ℝ H H * inner ℝ B B
    simpa only [pow_two] using real_inner_mul_inner_self_le H B
  have hVH : |g.inner p V H| ≤ w * k := by
    change |inner ℝ V H| ≤ w * k
    simpa only [hn, hV, hH] using abs_real_inner_le_norm V H
  have hRic (Y Z : TangentSpace (𝓡 n) p) :
      |D.ricci p Y Z| ≤ K * g.tangentNorm p Y * g.tangentNorm p Z := by
    have h := tensor_abs_le_of_unit_bound g D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) p
      (fun v hv => hBounds.ricci t ht' p (v 0) (v 1) (hv 0) (hv 1)) ![Y, Z]
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ, mul_assoc] using h
  have hRicBB : |D.ricci p B B| ≤ K * beta := by
    simpa only [hB, mul_assoc, ← pow_two, hu] using hRic B B
  have hr : |r x| ≤ K := by
    change |D.ricci p S S| ≤ K
    simpa only [hS, mul_one] using hRic S S
  have harc := m63TangentRicci_arc_abs_bounds F c hc hK hBounds ht x hSecond
  change |m62ArcDerivative F c t r x| ≤ K * (1 + 2 * k) ∧
    |m62ArcSecondDerivative F c t r x| ≤ K * (1 + 5 * k + 2 * u + 2 * q) at harc
  have hE := m63FirstJet_ambient_abs_bound F c hc hK hBounds ht x hRiemann hSecond
  change |E| ≤ K * beta + K * (2 * q + 10 * k + 3) * u at hE
  have heq := m63FirstJetSquared_evolution F c hc ht x
  change L = -2 * chi - 2 * D.ricci p B B + (2 * q + 6 * r x) * beta +
    12 * N ^ 2 + 6 * m62ArcDerivative F c t r x * N -
    4 * q * g.inner p V H - 2 * q * m62ArcSecondDerivative F c t r x + 2 * E at heq
  have hRicTerm : -2 * D.ricci p B B ≤ 2 * K * beta := by
    nlinarith only [(abs_le.mp hRicBB).1]
  have hrTerm : (2 * q + 6 * r x) * beta ≤ (2 * q + 6 * K) * beta := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mp hr).2 hbeta
    nlinarith only [h]
  have hcross : 6 * m62ArcDerivative F c t r x * N ≤
      6 * K * k * u + 12 * K * q * u := by
    have hmul : |m62ArcDerivative F c t r x * N| ≤ K * (1 + 2 * k) * (k * u) := by
      rw [abs_mul]
      exact mul_le_mul harc.1 hN (abs_nonneg _) (by positivity)
    calc
      _ ≤ 6 * (K * (1 + 2 * k) * (k * u)) := by
        nlinarith only [le_abs_self (m62ArcDerivative F c t r x * N), hmul]
      _ = _ := by rw [← hkq]; ring
  have hVTerm : -4 * q * g.inner p V H ≤ 4 * q * k * w := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hVH).1 (show 0 ≤ 4 * q by positivity)
    nlinarith only [h]
  have hsecondTerm : -2 * q * m62ArcSecondDerivative F c t r x ≤
      2 * q * K * (1 + 5 * k + 2 * u + 2 * q) := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp harc.2).1
      (show 0 ≤ 2 * q by positivity)
    nlinarith only [h]
  have hraw : L ≤ -2 * chi + (14 * q + 10 * K) * beta +
      K * (20 * q + 26 * k + 6) * u + 4 * q * k * w +
      2 * q * K * (1 + 5 * k + 2 * q) := by
    nlinarith only [heq, hRicTerm, hrTerm, hNsq, hcross, hVTerm,
      hsecondTerm, (abs_le.mp hE).2]
  have hqR : q ≤ R := hcurv
  have hkR : k ≤ R + 1 := by
    nlinarith only [hkq, hqR, sq_nonneg (k - 1)]
  have hq3 : q ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hq hqR 3
  have hYoung : 4 * q * k * w ≤ chi + 4 * q ^ 3 := by
    have hs : 0 ≤ 4 * q ^ 3 - 4 * q * k * w + chi := by
      calc
        _ = (2 * q * k - w) ^ 2 := by rw [← hkq, ← hw]; ring
        _ ≥ 0 := sq_nonneg _
    linarith only [hs]
  let A := 14 * R + 10 * K + 1
  let D0 := K * (46 * R + 32)
  let G := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + D0 ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hcoef : (14 * q + 10 * K) * beta ≤ (14 * R + 10 * K) * beta := by
    exact mul_le_mul_of_nonneg_right (by linarith only [hqR]) hbeta
  have hlinear : K * (20 * q + 26 * k + 6) * u ≤ D0 * u := by
    apply mul_le_mul_of_nonneg_right _ hun
    apply mul_le_mul_of_nonneg_left _ hK
    linarith only [hqR, hkR]
  have hconstant : 2 * q * K * (1 + 5 * k + 2 * q) ≤
      2 * R * K * (7 * R + 6) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqR (by norm_num)) hK
    · linarith only [hkR, hqR]
    · positivity
    · positivity
  have hlinearYoung : D0 * u ≤ beta + D0 ^ 2 := by
    nlinarith only [sq_nonneg (u - D0), hu, hbeta, sq_nonneg D0]
  have hbound : L ≤ -chi + A * beta + G := by
    dsimp only [A, G]
    nlinarith only [hraw, hYoung, hq3, hcoef, hlinear, hconstant, hlinearYoung]
  have hC : C = A + G := by dsimp only [C, A, G, D0]; ring
  rw [hC]
  nlinarith only [hbound, mul_nonneg hG hbeta, hA]

end PoincareConjecture
