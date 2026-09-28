import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.NormalizationJetBounds
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetErrorExpansion











set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63CurvatureJet_diffusionError_pair_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m : ℕ) (hm : 2 ≤ m)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hLower : ∀ i, i < m →
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c i t x) ≤ L)
    (hRm : ∀ d, d ≤ m →
      ∀ v : Fin (4 + d) → TangentSpace (𝓡 n) (c x t),
        (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
          |(F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation d (c x t) v| ≤ K)
    (hRic : ∀ d, d ≤ m + 1 →
      ∀ v : Fin (2 + d) → TangentSpace (𝓡 n) (c x t),
        (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
          |(F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).ricciEvaluation d (c x t) v| ≤ K) :
    let D := F.connection t
    let J := m63CurvatureJet F c m t x
    let Q := rampHorizontalCovariantDerivative D (fun s => c x s)
      (fun s => m63CurvatureJet F c m s x) t -
        m63CurvatureJet F c (m + 2) t x
    let w := (F.metric t).tangentNorm (c x t) J
    let z := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c (m + 1) t x)
    let D0 := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3) +
      (2 : ℝ) ^ (m + 1) * L ^ 2
    let D1 := (2 : ℝ) ^ (m + 2) * D0 * L +
      (m63JetErrorMassBound m : ℝ) * K * L ^ (m + 3)
    let T0 := (2 : ℝ) ^ (m + 1) * L ^ 3
    |(F.metric t).inner (c x t) Q J| ≤ T0 * z + D1 * (w + w ^ 2) := by
  classical
  let g := F.metric t
  let p := c x t
  let D := F.connection t
  let J := m63CurvatureJet F c
  let V : ℕ → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun i =>
    match i with
    | 0 => spatialUnitTangent F c t
    | r + 1 => J r t
  let N := fun i => g.tangentNorm p (J i t x)
  let w := N m
  let z := N (m + 1)
  let P := fun i => g.inner p (V i x) (J m t x)
  let Hpair := g.inner p (J 0 t x) (J (m + 1) t x)
  let A := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
  let Ar := fun r => ((m62ArcDerivative F c t)^[r]) A x
  let coeff := fun r => ((m + 2).choose (r + 1) : ℝ)
  let Q := rampHorizontalCovariantDerivative D (fun s => c x s)
    (fun s => J m s x) t - J (m + 2) t x
  let E := m63MarkedTensorExpression F c D.riemannEvaluation
      (m63RiemannJetErrorExpression m) t (J m t) x +
    m63MarkedTensorExpression F c D.ricciEvaluation
      (m63RicciJetErrorExpression m) t (J m t) x
  let D0 := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3) +
    (2 : ℝ) ^ (m + 1) * L ^ 2
  let Camb := (m63JetErrorMassBound m : ℝ) * K * L ^ (m + 3)
  let D1 := (2 : ℝ) ^ (m + 2) * D0 * L + Camb
  let T0 := (2 : ℝ) ^ (m + 1) * L ^ 3
  let C0 := D0 * L * (w + w ^ 2)
  have hN (i : ℕ) : 0 ≤ N i := Real.sqrt_nonneg _
  have hw : 0 ≤ w := hN m
  have hz : 0 ≤ z := hN (m + 1)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD0L : D0 ≤ D0 * L := by
    nlinarith only [mul_nonneg hD0 (sub_nonneg.mpr hL)]
  have hpoly : 0 ≤ w + w ^ 2 := add_nonneg hw (sq_nonneg w)
  have hC0 : 0 ≤ C0 := mul_nonneg (mul_nonneg hD0 hL0) hpoly
  have hunit : g.tangentNorm p (V 0 x) = 1 :=
    unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hinner (Y Z : TangentSpace (𝓡 n) p) :
      |g.inner p Y Z| ≤ g.tangentNorm p Y * g.tangentNorm p Z := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (W : TangentSpace (𝓡 n) p) : ‖W‖ = g.tangentNorm p W := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    change |inner ℝ Y Z| ≤ _
    simpa only [hn] using abs_real_inner_le_norm Y Z
  have hP0 : |P 0| ≤ w := by
    have h := hinner (V 0 x) (J m t x)
    simpa only [hunit, one_mul] using h
  have hPm : |P (m + 1)| ≤ w ^ 2 := by
    simpa only [P, V, ← pow_two] using hinner (J m t x) (J m t x)
  have hPLower (i : ℕ) (hi : i < m) : |P (i + 1)| ≤ L * w :=
    (hinner (J i t x) (J m t x)).trans
      (mul_le_mul_of_nonneg_right (hLower i hi) hw)
  have hnorm := m63Normalization_arc_iterate_bounds F c hc m hm hK hL ht x hLower hRic
  change (∀ r, r < m → |Ar r| ≤ D0) ∧ |Ar m| ≤ D0 * (1 + w) ∧
    |Ar (m + 1) - 2 * Hpair| ≤ D0 * (1 + w) at hnorm
  have hrow (r : ℕ) (hr : r ≤ m) : |Ar r * P (m + 1 - r)| ≤ C0 := by
    by_cases hr0 : r = 0
    · subst r
      simp only [Nat.sub_zero]
      have hb := mul_le_mul (hnorm.1 0 (by omega)) hPm (abs_nonneg _) hD0
      rw [← abs_mul] at hb
      calc
        _ ≤ D0 * w ^ 2 := hb
        _ ≤ D0 * (w + w ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hw]) hD0
        _ ≤ C0 := mul_le_mul_of_nonneg_right hD0L hpoly
    · by_cases hrm : r = m
      · subst r
        have hindex : m + 1 - m = 1 := by omega
        rw [hindex]
        have hb := mul_le_mul hnorm.2.1 (hPLower 0 (by omega))
          (abs_nonneg _) (mul_nonneg hD0 (by positivity))
        rw [← abs_mul] at hb
        exact hb.trans_eq (by dsimp only [C0]; ring)
      · have hrlt : r < m := by omega
        have hindex : m + 1 - r = (m - r) + 1 := by omega
        rw [hindex]
        have hb := mul_le_mul (hnorm.1 r hrlt) (hPLower (m - r) (by omega))
          (abs_nonneg _) hD0
        rw [← abs_mul] at hb
        calc
          _ ≤ D0 * (L * w) := hb
          _ ≤ C0 := by
            have h := mul_nonneg (mul_nonneg hD0 hL0) (sq_nonneg w)
            dsimp only [C0]
            nlinarith only [h]
  have hmass (k : ℕ) :
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  have htangent : |P 0| ≤ (2 : ℝ) ^ m * L ^ 2 := by
    have htan := m63CurvatureJet_tangent_abs_le F c hc (m - 1) ht x
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at htan
    change |g.inner p (J m t x) (V 0 x)| ≤
      ∑ i ∈ Finset.range m, (m.choose i : ℝ) * N i * N (m - 1 - i) at htan
    have hsym : P 0 = g.inner p (J m t x) (V 0 x) := g.symm p _ _
    rw [hsym]
    calc
      _ ≤ ∑ i ∈ Finset.range m, (m.choose i : ℝ) * N i * N (m - 1 - i) := htan
      _ ≤ ∑ i ∈ Finset.range m, (m.choose i : ℝ) * L ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have him := Finset.mem_range.mp hi
        have hprod := mul_le_mul (hLower i him) (hLower (m - 1 - i) (by omega))
          (hN (m - 1 - i)) hL0
        have h := mul_le_mul_of_nonneg_left hprod
          (Nat.cast_nonneg (m.choose i) : (0 : ℝ) ≤ _)
        simpa only [mul_assoc, pow_two] using h
      _ = (∑ i ∈ Finset.range m, (m.choose i : ℝ)) * L ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_succ m)) (fun i _ _ => Nat.cast_nonneg _))
          (sq_nonneg L)
      _ = (2 : ℝ) ^ m * L ^ 2 := by rw [hmass]
  let lead := 2 * Hpair * P 0
  have hHpair : |Hpair| ≤ L * z :=
    (hinner (J 0 t x) (J (m + 1) t x)).trans
      (mul_le_mul_of_nonneg_right (hLower 0 (by omega)) hz)
  have hlead : |lead| ≤ T0 * z := by
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left hHpair (by norm_num : (0 : ℝ) ≤ 2)) htangent
      (abs_nonneg (P 0)) (by positivity)
    calc
      |lead| = 2 * |Hpair| * |P 0| := by
        simp only [lead, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (L * z) * ((2 : ℝ) ^ m * L ^ 2) := h
      _ = T0 * z := by dsimp only [T0]; rw [pow_succ]; ring
  have hrem : |Ar (m + 1) * P 0 - lead| ≤ C0 := by
    rw [show Ar (m + 1) * P 0 - lead = (Ar (m + 1) - 2 * Hpair) * P 0 by
      dsimp only [lead]
      ring]
    rw [abs_mul]
    calc
      _ ≤ (D0 * (1 + w)) * w :=
        mul_le_mul hnorm.2.2 hP0 (abs_nonneg _) (mul_nonneg hD0 (by positivity))
      _ = D0 * (w + w ^ 2) := by ring
      _ ≤ C0 := mul_le_mul_of_nonneg_right hD0L hpoly
  have htop : |Ar (m + 1) * P 0| ≤ C0 + T0 * z := by
    calc
      _ = |(Ar (m + 1) * P 0 - lead) + lead| := by congr 1; ring
      _ ≤ |Ar (m + 1) * P 0 - lead| + |lead| := abs_add_le _ _
      _ ≤ C0 + T0 * z := add_le_add hrem hlead
  have hcoeff (r : ℕ) : 0 ≤ coeff r := Nat.cast_nonneg _
  have hcoeffTop : coeff (m + 1) = 1 := by
    simp only [coeff, Nat.add_assoc, Nat.choose_self, Nat.cast_one]
  have hshiftmass : (∑ r ∈ Finset.range (m + 2), coeff r) ≤ (2 : ℝ) ^ (m + 2) := by
    have h := hmass (m + 2)
    rw [Finset.sum_range_succ'] at h
    change (∑ r ∈ Finset.range (m + 2), coeff r) +
      ((m + 2).choose 0 : ℝ) = (2 : ℝ) ^ (m + 2) at h
    have hnon := (Nat.cast_nonneg ((m + 2).choose 0) : (0 : ℝ) ≤ _)
    linarith only [h, hnon]
  have hmassLow : (∑ r ∈ Finset.range (m + 1), coeff r) + 1 ≤
      (2 : ℝ) ^ (m + 2) := by
    rwa [Finset.sum_range_succ, hcoeffTop] at hshiftmass
  have hsumLow : |∑ r ∈ Finset.range (m + 1), coeff r * Ar r * P (m + 1 - r)| ≤
      (∑ r ∈ Finset.range (m + 1), coeff r) * C0 := by
    calc
      _ ≤ ∑ r ∈ Finset.range (m + 1), |coeff r * Ar r * P (m + 1 - r)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.range (m + 1), coeff r * C0 := by
        apply Finset.sum_le_sum
        intro r hr
        have h := mul_le_mul_of_nonneg_left (hrow r (by
          have := Finset.mem_range.mp hr
          omega)) (hcoeff r)
        simpa only [abs_mul, abs_of_nonneg (hcoeff r), mul_assoc] using h
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hsplit : (∑ r ∈ Finset.range (m + 2), coeff r * Ar r * P (m + 1 - r)) =
      (∑ r ∈ Finset.range (m + 1), coeff r * Ar r * P (m + 1 - r)) +
        Ar (m + 1) * P 0 := by
    rw [Finset.sum_range_succ, hcoeffTop, one_mul, Nat.sub_self]
  have hsum : |∑ r ∈ Finset.range (m + 2), coeff r * Ar r * P (m + 1 - r)| ≤
      (2 : ℝ) ^ (m + 2) * C0 + T0 * z := by
    rw [hsplit]
    calc
      _ ≤ |∑ r ∈ Finset.range (m + 1), coeff r * Ar r * P (m + 1 - r)| +
          |Ar (m + 1) * P 0| := abs_add_le _ _
      _ ≤ (∑ r ∈ Finset.range (m + 1), coeff r) * C0 + (C0 + T0 * z) :=
        add_le_add hsumLow htop
      _ = ((∑ r ∈ Finset.range (m + 1), coeff r) + 1) * C0 + T0 * z := by ring
      _ ≤ (2 : ℝ) ^ (m + 2) * C0 + T0 * z :=
        add_le_add (mul_le_mul_of_nonneg_right hmassLow hC0) le_rfl
  have hE := m63CurvatureJet_ambientError_abs_le F c hc m hK hL ht x
    hLower hRm hRic (J m t)
  change |E| ≤ Camb * (1 + w) * w at hE
  have hrep := m63CurvatureJet_diffusionError_expansion_pair F c hc m m ht x
  change g.inner p Q (J m t x) =
    (∑ r ∈ Finset.range (m + 2), coeff r * Ar r * P (m + 1 - r)) + E at hrep
  change |g.inner p Q (J m t x)| ≤ T0 * z + D1 * (w + w ^ 2)
  rw [hrep]
  exact ((abs_add_le _ _).trans (add_le_add hsum hE)).trans_eq (by
    dsimp only [D1, C0]
    ring)




theorem m63CurvatureJetSquared_dissipation_of_lower_bounds [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m : ℕ) (hm : 2 ≤ m)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hLower : ∀ i, i < m →
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c i t x) ≤ L)
    (hRm : ∀ d, d ≤ m →
      ∀ v : Fin (4 + d) → TangentSpace (𝓡 n) (c x t),
        (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
          |(F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).riemannEvaluation d (c x t) v| ≤ K)
    (hRic : ∀ d, d ≤ m + 1 →
      ∀ v : Fin (2 + d) → TangentSpace (𝓡 n) (c x t),
        (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
          |(F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).ricciEvaluation d (c x t) v| ≤ K) :
    let D0 := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3) +
      (2 : ℝ) ^ (m + 1) * L ^ 2
    let D1 := (2 : ℝ) ^ (m + 2) * D0 * L +
      (m63JetErrorMassBound m : ℝ) * K * L ^ (m + 3)
    let T0 := (2 : ℝ) ^ (m + 1) * L ^ 3
    let C := 2 * K + 4 * D1 + T0 ^ 2
    0 ≤ C ∧
      deriv (fun s => m63CurvatureJetSquared F c m s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c m t) x ≤
      -m63CurvatureJetSquared F c (m + 1) t x +
        C * m63CurvatureJetSquared F c m t x + C := by
  let g := F.metric t
  let p := c x t
  let D := F.connection t
  let J := m63CurvatureJet F c m t x
  let Jnext := m63CurvatureJet F c (m + 1) t x
  let Q := rampHorizontalCovariantDerivative D (fun s => c x s)
    (fun s => m63CurvatureJet F c m s x) t - m63CurvatureJet F c (m + 2) t x
  let w := g.tangentNorm p J
  let z := g.tangentNorm p Jnext
  let D0 := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3) +
    (2 : ℝ) ^ (m + 1) * L ^ 2
  let D1 := (2 : ℝ) ^ (m + 2) * D0 * L +
    (m63JetErrorMassBound m : ℝ) * K * L ^ (m + 3)
  let T0 := (2 : ℝ) ^ (m + 1) * L ^ 3
  let C := 2 * K + 4 * D1 + T0 ^ 2
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD1 : 0 ≤ D1 := by dsimp only [D1]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hw2 : w ^ 2 = m63CurvatureJetSquared F c m t x :=
    Real.sq_sqrt ((g.toRiemannianMetric.toCore p).re_inner_nonneg J)
  have hz2 : z ^ 2 = m63CurvatureJetSquared F c (m + 1) t x :=
    Real.sq_sqrt ((g.toRiemannianMetric.toCore p).re_inner_nonneg Jnext)
  have hpair := m63CurvatureJet_diffusionError_pair_bound F c hc m hm hK hL ht x
    hLower hRm hRic
  change |g.inner p Q J| ≤ T0 * z + D1 * (w + w ^ 2) at hpair
  have hRic0 : ∀ v : Fin 2 → TangentSpace (𝓡 n) p,
      (∀ i, g.tangentNorm p (v i) ≤ 1) → |D.ricciEvaluation p v| ≤ K :=
    hRic 0 (by omega)
  have hr := tensor_abs_le_of_unit_bound g D.ricciEvaluation
    (M04.isSmoothCovariantTensor_ricciEvaluation D) p hRic0 ![J, J]
  have hr' : |D.ricci p J J| ≤ K * w ^ 2 := by
    simpa only [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      mul_one, w, pow_two] using hr
  have hdiff := m63CurvatureJetSquared_diffusion_identity F c hc m ht x
  change deriv (fun s => m63CurvatureJetSquared F c m s x) t -
    m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c m t) x =
      -2 * m63CurvatureJetSquared F c (m + 1) t x - 2 * D.ricci p J J +
        2 * g.inner p Q J at hdiff
  change 0 ≤ C ∧ _
  refine ⟨hC, ?_⟩
  rw [← hw2, ← hz2]
  have hraw : deriv (fun s => m63CurvatureJetSquared F c m s x) t -
      m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c m t) x ≤
      -z ^ 2 + (2 * K + 3 * D1) * w ^ 2 + D1 + T0 ^ 2 := by
    nlinarith only [hdiff, hz2, (abs_le.mp hr').1, (abs_le.mp hpair).2,
      sq_nonneg (z - T0), mul_nonneg hD1 (sq_nonneg (w - 1))]
  nlinarith only [hraw, hK, hD1, sq_nonneg T0,
    mul_nonneg (add_nonneg hD1 (sq_nonneg T0)) (sq_nonneg w)]

end PoincareConjecture
