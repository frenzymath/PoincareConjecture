import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ScaledNormalizationJetBounds
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




theorem m63CurvatureJetSquared_scaled_dissipation_of_lower_bounds [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m : ℕ) (hm : 2 ≤ m)
    {rho K L : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hK : 0 ≤ K) (hL : 1 ≤ L)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hLower : ∀ i, i < m → rho ^ (i + 1) *
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
      rho ^ (2 * m + 4) *
          (deriv (fun s => m63CurvatureJetSquared F c m s x) t -
            m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c m t) x) ≤
        -(rho ^ (2 * m + 4) * m63CurvatureJetSquared F c (m + 1) t x) +
          C * (rho ^ (2 * m + 2) * m63CurvatureJetSquared F c m t x) + C := by
  classical
  let g := F.metric t
  let p := c x t
  let D := F.connection t
  let J := m63CurvatureJet F c
  let V : ℕ → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun i =>
    match i with
    | 0 => spatialUnitTangent F c t
    | j + 1 => J j t
  let N := fun i => rho ^ (i + 1) * g.tangentNorm p (J i t x)
  let VN := fun i => rho ^ i * g.tangentNorm p (V i x)
  let w := N m
  let z := N (m + 1)
  let P := fun i => rho ^ (i + m + 1) * g.inner p (V i x) (J m t x)
  let Hpair := rho ^ (m + 3) * g.inner p (J 0 t x) (J (m + 1) t x)
  let A := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
  let Ar := fun r => rho ^ (r + 2) * ((m62ArcDerivative F c t)^[r]) A x
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
  let C := 2 * K + 4 * D1 + T0 ^ 2
  let C0 := D0 * L * (w + w ^ 2)
  have hN (i : ℕ) : 0 ≤ N i :=
    mul_nonneg (pow_nonneg hrho.le _) (Real.sqrt_nonneg _)
  have hVN (i : ℕ) : 0 ≤ VN i :=
    mul_nonneg (pow_nonneg hrho.le _) (Real.sqrt_nonneg _)
  have hw : 0 ≤ w := hN m
  have hz : 0 ≤ z := hN (m + 1)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD1 : 0 ≤ D1 := by dsimp only [D1, Camb]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD0L : D0 ≤ D0 * L := by
    nlinarith only [mul_nonneg hD0 (sub_nonneg.mpr hL)]
  have hpoly : 0 ≤ w + w ^ 2 := add_nonneg hw (sq_nonneg w)
  have hC0 : 0 ≤ C0 := mul_nonneg (mul_nonneg hD0 hL0) hpoly
  have hunit : g.tangentNorm p (V 0 x) = 1 :=
    unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hVNzero : VN 0 = 1 := by simp only [VN, pow_zero, one_mul, hunit]
  have hVNlower (i : ℕ) (hi : i ≤ m) : VN i ≤ L := by
    cases i with
    | zero => exact hVNzero.le.trans hL
    | succ i => exact hLower i (by omega)
  have hinner (Y Z : TangentSpace (𝓡 n) p) :
      |g.inner p Y Z| ≤ g.tangentNorm p Y * g.tangentNorm p Z := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (W : TangentSpace (𝓡 n) p) : ‖W‖ = g.tangentNorm p W := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    change |inner ℝ Y Z| ≤ _
    simpa only [hn] using abs_real_inner_le_norm Y Z
  have hPinner (i : ℕ) : |P i| ≤ VN i * w := by
    calc
      _ = rho ^ (i + m + 1) * |g.inner p (V i x) (J m t x)| := by
        simp only [P, abs_mul, abs_pow, abs_of_pos hrho]
      _ ≤ rho ^ (i + m + 1) * (g.tangentNorm p (V i x) * g.tangentNorm p (J m t x)) :=
        mul_le_mul_of_nonneg_left (hinner _ _) (pow_nonneg hrho.le _)
      _ = VN i * w := by
        dsimp only [VN, w, N]
        rw [show i + m + 1 = i + (m + 1) by omega, pow_add]
        ring
  have hP0 : |P 0| ≤ w := by simpa only [hVNzero, one_mul] using hPinner 0
  have hPm : |P (m + 1)| ≤ w ^ 2 := by
    simpa only [VN, V, N, w, ← pow_two] using hPinner (m + 1)
  have hPLower (i : ℕ) (hi : i < m) : |P (i + 1)| ≤ L * w :=
    (hPinner (i + 1)).trans (mul_le_mul_of_nonneg_right (hLower i hi) hw)
  have hnormRaw := m63Normalization_arc_iterate_scaled_bounds F c hc m hm
    hrho hrho1 hK hL ht x hLower hRic
  have hnorm : (∀ r, r < m → |Ar r| ≤ D0) ∧ |Ar m| ≤ D0 * (1 + w) ∧
      |Ar (m + 1) - 2 * Hpair| ≤ D0 * (1 + w) := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simpa only [Ar, abs_mul, abs_pow, abs_of_pos hrho] using hnormRaw.1 r hr
    · simpa only [Ar, abs_mul, abs_pow, abs_of_pos hrho] using hnormRaw.2.1
    · have heq : Ar (m + 1) - 2 * Hpair = rho ^ (m + 3) *
          (((m62ArcDerivative F c t)^[m + 1]) A x -
            2 * g.inner p (J 0 t x) (J (m + 1) t x)) := by
        dsimp only [Ar, Hpair]
        ring
      rw [heq, abs_mul, abs_pow, abs_of_pos hrho]
      exact hnormRaw.2.2
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
        rw [show m + 1 - m = 1 by omega]
        have hb := mul_le_mul hnorm.2.1 (hPLower 0 (by omega))
          (abs_nonneg _) (mul_nonneg hD0 (by positivity))
        rw [← abs_mul] at hb
        exact hb.trans_eq (by dsimp only [C0]; ring)
      · have hrlt : r < m := by omega
        rw [show m + 1 - r = (m - r) + 1 by omega]
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
      ∑ i ∈ Finset.range m, (m.choose i : ℝ) *
        g.tangentNorm p (J i t x) * g.tangentNorm p (J (m - 1 - i) t x) at htan
    have hsym : g.inner p (V 0 x) (J m t x) = g.inner p (J m t x) (V 0 x) :=
      g.symm p _ _
    calc
      _ = rho ^ (m + 1) * |g.inner p (J m t x) (V 0 x)| := by
        simp only [P, zero_add, abs_mul, abs_pow, abs_of_pos hrho, hsym]
      _ ≤ rho ^ (m + 1) *
          ∑ i ∈ Finset.range m, (m.choose i : ℝ) *
            g.tangentNorm p (J i t x) * g.tangentNorm p (J (m - 1 - i) t x) :=
        mul_le_mul_of_nonneg_left htan (pow_nonneg hrho.le _)
      _ = ∑ i ∈ Finset.range m, (m.choose i : ℝ) * N i * N (m - 1 - i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have him := Finset.mem_range.mp hi
        dsimp only [N]
        rw [show m + 1 = (i + 1) + (m - 1 - i + 1) by omega, pow_add]
        ring
      _ ≤ ∑ i ∈ Finset.range m, (m.choose i : ℝ) * L ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have him := Finset.mem_range.mp hi
        have hprod := mul_le_mul (hLower i him) (hLower (m - 1 - i) (by omega))
          (hN (m - 1 - i)) hL0
        have h := mul_le_mul_of_nonneg_left hprod
          (Nat.cast_nonneg (m.choose i) : (0 : ℝ) ≤ _)
        simpa only [N, g, p, J, mul_assoc, pow_two] using h
      _ = (∑ i ∈ Finset.range m, (m.choose i : ℝ)) * L ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_succ m)) (fun i _ _ => Nat.cast_nonneg _))
          (sq_nonneg L)
      _ = (2 : ℝ) ^ m * L ^ 2 := by rw [hmass]
  let lead := 2 * Hpair * P 0
  have hHpair : |Hpair| ≤ L * z := by
    have hb : |Hpair| ≤ N 0 * z := by
      calc
        _ = rho ^ (m + 3) * |g.inner p (J 0 t x) (J (m + 1) t x)| := by
          simp only [Hpair, abs_mul, abs_pow, abs_of_pos hrho]
        _ ≤ rho ^ (m + 3) *
            (g.tangentNorm p (J 0 t x) * g.tangentNorm p (J (m + 1) t x)) :=
          mul_le_mul_of_nonneg_left (hinner _ _) (pow_nonneg hrho.le _)
        _ = N 0 * z := by
          dsimp only [N, z]
          rw [show m + 3 = (0 + 1) + (m + 1 + 1) by omega, pow_add]
          ring
    exact hb.trans (mul_le_mul_of_nonneg_right (hLower 0 (by omega)) hz)
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
  have hE : rho ^ (2 * m + 4) * |E| ≤ Camb * (1 + w) * w := by
    let Cb := K * L ^ (m + 3) * (1 + w) * w
    have hpow : 1 ≤ L ^ (m + 3) := by
      simpa only [pow_zero] using pow_le_pow_right₀ hL (Nat.zero_le (m + 3))
    have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
    have hprod {k : ℕ} (s : Finset (Fin k)) (f : Fin k → ℕ)
        (hweight : ∑ i ∈ s, f i ≤ m + 1) (hcard : s.card ≤ m + 3) :
        ∏ i ∈ s, VN (f i) ≤ L ^ (m + 3) * (1 + w) := by
      by_cases hex : ∃ i ∈ s, f i = m + 1
      · obtain ⟨i, hi, hfi⟩ := hex
        have hsum := Finset.sum_erase_add s f hi
        have hzero (j : Fin k) (hj : j ∈ s.erase i) : f j = 0 := by
          have hle := Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hj
          omega
        have hrest : ∏ j ∈ s.erase i, VN (f j) = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          rw [hzero j hj, hVNzero]
        rw [← Finset.prod_erase_mul s (fun j => VN (f j)) hi, hrest, one_mul, hfi]
        change w ≤ _
        nlinarith only [hpow, hw]
      · have hsmall (i : Fin k) (hi : i ∈ s) : f i ≤ m := by
          have hle := Finset.single_le_sum (fun r _ => Nat.zero_le (f r)) hi
          have hne : f i ≠ m + 1 := fun h => hex ⟨i, hi, h⟩
          omega
        have hp := Finset.prod_le_prod (fun i _ => hVN (f i))
          (fun i hi => hVNlower (f i) (hsmall i hi))
        have hp' := (hp.trans_eq (Finset.prod_const L)).trans (pow_le_pow_right₀ hL hcard)
        nlinarith only [hp', hpow, hw]
    have hterm {k : ℕ} (T : CovariantTensorEvaluation n M k)
        (hT : IsSmoothCovariantTensor T) (B : MarkedTensorContraction k)
        (hweight : B.weight = m + 1) (hrank : k + B.order ≤ m + 4)
        (hbound : ∀ v : Fin (k + B.order) → TangentSpace (𝓡 n) (c x t),
          (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
            |D.iteratedCovariantTensorDerivative T B.order (c x t) v| ≤ K) :
        rho ^ (2 * m + 4) * |m63MarkedTensorTerm F c T B t (J m t) x| ≤ Cb := by
      have hiter (d : ℕ) : IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T d) := by
        induction d with
        | zero => exact hT
        | succ d ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
      let vec := fun i => if i = B.test then J m t x else V (B.jet i) x
      have hb := tensor_abs_le_of_unit_bound (F.metric t)
        (D.iteratedCovariantTensorDerivative T B.order) (hiter _) (c x t) hbound vec
      have hp := hprod (Finset.univ.erase B.test) B.jet
        ((Nat.le_add_left _ _).trans_eq hweight)
        (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]; omega)
      have heq : (∏ i, g.tangentNorm p (vec i)) =
          (∏ i ∈ Finset.univ.erase B.test, g.tangentNorm p (V (B.jet i) x)) *
            g.tangentNorm p (J m t x) := by
        rw [← Finset.prod_erase_mul Finset.univ
          (fun i => g.tangentNorm p (vec i)) (Finset.mem_univ B.test)]
        have hmark : g.tangentNorm p (vec B.test) = g.tangentNorm p (J m t x) := by
          simp only [vec, if_true]
        rw [hmark]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp only [vec, (Finset.mem_erase.mp hi).1, if_false]
      have heval : m63MarkedTensorTerm F c T B t (J m t) x =
          D.iteratedCovariantTensorDerivative T B.order (c x t) vec := by
        have htuple : (fun i : Fin (k + B.order) =>
            if i = B.test then J m t x else
              match B.jet i with
              | 0 => spatialUnitTangent F c t x
              | j + 1 => J j t x) = vec := by
          funext i
          dsimp only [vec]
          split_ifs
          · rfl
          · cases hidx : B.jet i <;> rfl
        exact congrArg (D.iteratedCovariantTensorDerivative T B.order (c x t)) htuple
      rw [← heval] at hb
      change |m63MarkedTensorTerm F c T B t (J m t) x| ≤
        K * ∏ i, g.tangentNorm p (vec i) at hb
      rw [heq] at hb
      have hpowers : (∏ i ∈ Finset.univ.erase B.test, VN (B.jet i)) =
          rho ^ (∑ i ∈ Finset.univ.erase B.test, B.jet i) *
            ∏ i ∈ Finset.univ.erase B.test, g.tangentNorm p (V (B.jet i) x) := by
        dsimp only [VN]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      have hweight' : B.order + ∑ i ∈ Finset.univ.erase B.test, B.jet i = m + 1 := hweight
      calc
        _ ≤ rho ^ (2 * m + 4) * (K *
            ((∏ i ∈ Finset.univ.erase B.test, g.tangentNorm p (V (B.jet i) x)) *
              g.tangentNorm p (J m t x))) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg hrho.le _)
        _ = rho ^ (B.order + 2) *
            (K * (∏ i ∈ Finset.univ.erase B.test, VN (B.jet i)) * w) := by
          rw [hpowers]
          dsimp only [w, N]
          rw [show 2 * m + 4 = (B.order + 2) +
            (∑ i ∈ Finset.univ.erase B.test, B.jet i) + (m + 1) by omega,
            pow_add, pow_add]
          ring
        _ ≤ 1 * (K * (∏ i ∈ Finset.univ.erase B.test, VN (B.jet i)) * w) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hrho.le hrho1)
            (mul_nonneg (mul_nonneg hK (Finset.prod_nonneg (fun i _ => hVN _))) hw)
        _ = K * (∏ i ∈ Finset.univ.erase B.test, VN (B.jet i)) * w := one_mul _
        _ ≤ K * (L ^ (m + 3) * (1 + w)) * w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK) hw
        _ = Cb := by dsimp only [Cb]; ring
    have hlist {k : ℕ} (T : CovariantTensorEvaluation n M k)
        (R : List (Int × MarkedTensorContraction k))
        (hR : ∀ e ∈ R, rho ^ (2 * m + 4) * |m63MarkedTensorTerm F c T e.2 t (J m t) x| ≤ Cb) :
        rho ^ (2 * m + 4) * |m63MarkedTensorExpression F c T R t (J m t) x| ≤
          (markedTensorCoefficientMass R : ℝ) * Cb := by
      induction R with
      | nil => simp [m63MarkedTensorExpression, markedTensorCoefficientMass]
      | cons e R ih =>
        have hp := ih (fun r hr => hR r (List.mem_cons_of_mem e hr))
        have he := mul_le_mul_of_nonneg_left (hR e List.mem_cons_self) (abs_nonneg (e.1 : ℝ))
        have hcast : |(e.1 : ℝ)| = (e.1.natAbs : ℝ) := by
          simp only [Nat.cast_natAbs, Int.cast_abs]
        have he' : rho ^ (2 * m + 4) *
            |(e.1 : ℝ) * m63MarkedTensorTerm F c T e.2 t (J m t) x| ≤
              (e.1.natAbs : ℝ) * Cb := by
          calc
            _ = |(e.1 : ℝ)| * (rho ^ (2 * m + 4) *
                |m63MarkedTensorTerm F c T e.2 t (J m t) x|) := by rw [abs_mul]; ring
            _ ≤ _ := by simpa only [hcast] using he
        change rho ^ (2 * m + 4) * |(e.1 : ℝ) * m63MarkedTensorTerm F c T e.2 t (J m t) x +
          m63MarkedTensorExpression F c T R t (J m t) x| ≤ _
        calc
          _ ≤ rho ^ (2 * m + 4) * (|(e.1 : ℝ) * m63MarkedTensorTerm F c T e.2 t (J m t) x| +
              |m63MarkedTensorExpression F c T R t (J m t) x|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (pow_nonneg hrho.le _)
          _ = rho ^ (2 * m + 4) * |(e.1 : ℝ) * m63MarkedTensorTerm F c T e.2 t (J m t) x| +
              rho ^ (2 * m + 4) * |m63MarkedTensorExpression F c T R t (J m t) x| := mul_add _ _ _
          _ ≤ (e.1.natAbs : ℝ) * Cb + (markedTensorCoefficientMass R : ℝ) * Cb :=
            add_le_add he' hp
          _ = _ := by simp only [markedTensorCoefficientMass, List.map_cons,
            List.sum_cons, Nat.cast_add, add_mul]
    have hs := m63JetErrorExpression_spec m
    have hr := hlist D.riemannEvaluation (m63RiemannJetErrorExpression m) (by
      intro e he
      exact hterm _ (M04.isSmoothCovariantTensor_riemannEvaluation D) e.2 (hs.1 e he).1
        (by have := (hs.1 e he).2; omega) (hRm e.2.order (hs.1 e he).2))
    have hi := hlist D.ricciEvaluation (m63RicciJetErrorExpression m) (by
      intro e he
      exact hterm _ (M04.isSmoothCovariantTensor_ricciEvaluation D) e.2 (hs.2.1 e he).1
        (by have := (hs.2.1 e he).2; omega) (hRic e.2.order (hs.2.1 e he).2))
    have hmass' : (markedTensorCoefficientMass (m63RiemannJetErrorExpression m) : ℝ) +
        (markedTensorCoefficientMass (m63RicciJetErrorExpression m) : ℝ) ≤
          (m63JetErrorMassBound m : ℝ) := by exact_mod_cast hs.2.2
    calc
      _ ≤ rho ^ (2 * m + 4) *
          (|m63MarkedTensorExpression F c D.riemannEvaluation
            (m63RiemannJetErrorExpression m) t (J m t) x| +
            |m63MarkedTensorExpression F c D.ricciEvaluation
              (m63RicciJetErrorExpression m) t (J m t) x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (pow_nonneg hrho.le _)
      _ = _ := mul_add _ _ _
      _ ≤ (markedTensorCoefficientMass (m63RiemannJetErrorExpression m) : ℝ) * Cb +
          (markedTensorCoefficientMass (m63RicciJetErrorExpression m) : ℝ) * Cb := add_le_add hr hi
      _ ≤ (m63JetErrorMassBound m : ℝ) * Cb := by
        simpa only [add_mul] using mul_le_mul_of_nonneg_right hmass' hCb
      _ = Camb * (1 + w) * w := by dsimp only [Cb, Camb]; ring
  have hrep := m63CurvatureJet_diffusionError_expansion_pair F c hc m m ht x
  have hrepScaled : rho ^ (2 * m + 4) * g.inner p Q (J m t x) =
      (∑ r ∈ Finset.range (m + 2), coeff r * Ar r * P (m + 1 - r)) +
        rho ^ (2 * m + 4) * E := by
    change g.inner p Q (J m t x) =
      (∑ r ∈ Finset.range (m + 2), coeff r *
        (((m62ArcDerivative F c t)^[r]) A x) * g.inner p (V (m + 1 - r) x) (J m t x)) + E at hrep
    rw [hrep, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hrle : r ≤ m + 1 := by have := Finset.mem_range.mp hr; omega
    dsimp only [Ar, P]
    rw [show 2 * m + 4 = (r + 2) + (m + 1 - r + m + 1) by omega, pow_add]
    ring
  have hpair : |rho ^ (2 * m + 4) * g.inner p Q (J m t x)| ≤
      T0 * z + D1 * (w + w ^ 2) := by
    rw [hrepScaled]
    have hE' : |rho ^ (2 * m + 4) * E| ≤ Camb * (1 + w) * w := by
      simpa only [abs_mul, abs_pow, abs_of_pos hrho] using hE
    exact ((abs_add_le _ _).trans (add_le_add hsum hE')).trans_eq (by
      dsimp only [D1, C0]
      ring)
  have hw2 : w ^ 2 = rho ^ (2 * m + 2) * m63CurvatureJetSquared F c m t x := by
    have hn : (g.tangentNorm p (J m t x)) ^ 2 = m63CurvatureJetSquared F c m t x :=
      Real.sq_sqrt ((g.toRiemannianMetric.toCore p).re_inner_nonneg (J m t x))
    dsimp only [w, N]
    rw [mul_pow, hn, ← pow_mul, show (m + 1) * 2 = 2 * m + 2 by omega]
  have hz2 : z ^ 2 = rho ^ (2 * m + 4) * m63CurvatureJetSquared F c (m + 1) t x := by
    have hn : (g.tangentNorm p (J (m + 1) t x)) ^ 2 =
        m63CurvatureJetSquared F c (m + 1) t x :=
      Real.sq_sqrt ((g.toRiemannianMetric.toCore p).re_inner_nonneg (J (m + 1) t x))
    dsimp only [z, N]
    rw [mul_pow, hn, ← pow_mul, show (m + 1 + 1) * 2 = 2 * m + 4 by omega]
  have hRic0 : ∀ v : Fin 2 → TangentSpace (𝓡 n) p,
      (∀ i, g.tangentNorm p (v i) ≤ 1) → |D.ricciEvaluation p v| ≤ K :=
    hRic 0 (by omega)
  have hr := tensor_abs_le_of_unit_bound g D.ricciEvaluation
    (M04.isSmoothCovariantTensor_ricciEvaluation D) p hRic0 ![J m t x, J m t x]
  have hrRaw : |D.ricci p (J m t x) (J m t x)| ≤ K * (g.tangentNorm p (J m t x)) ^ 2 := by
    simpa only [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      mul_one, pow_two] using hr
  have hr' : |rho ^ (2 * m + 4) * D.ricci p (J m t x) (J m t x)| ≤ K * w ^ 2 := by
    calc
      _ = rho ^ (2 * m + 4) * |D.ricci p (J m t x) (J m t x)| := by
        simp only [abs_mul, abs_pow, abs_of_pos hrho]
      _ ≤ rho ^ (2 * m + 4) * (K * (g.tangentNorm p (J m t x)) ^ 2) :=
        mul_le_mul_of_nonneg_left hrRaw (pow_nonneg hrho.le _)
      _ = rho ^ 2 * (K * w ^ 2) := by
        dsimp only [w, N]
        rw [mul_pow, ← pow_mul,
          show 2 * m + 4 = 2 + (m + 1) * 2 by omega, pow_add]
        ring
      _ ≤ 1 * (K * w ^ 2) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hrho.le hrho1) (mul_nonneg hK (sq_nonneg w))
      _ = _ := one_mul _
  have hdiff := m63CurvatureJetSquared_diffusion_identity F c hc m ht x
  have hdiffScaled : rho ^ (2 * m + 4) *
      (deriv (fun s => m63CurvatureJetSquared F c m s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c m t) x) =
      -2 * z ^ 2 - 2 * (rho ^ (2 * m + 4) * D.ricci p (J m t x) (J m t x)) +
        2 * (rho ^ (2 * m + 4) * g.inner p Q (J m t x)) := by
    rw [hdiff, hz2]
    change rho ^ (2 * m + 4) *
      (-2 * m63CurvatureJetSquared F c (m + 1) t x - 2 * D.ricci p (J m t x) (J m t x) +
        2 * g.inner p Q (J m t x)) = _
    ring
  change 0 ≤ C ∧ _
  refine ⟨hC, ?_⟩
  rw [← hw2, ← hz2]
  have hraw : rho ^ (2 * m + 4) *
      (deriv (fun s => m63CurvatureJetSquared F c m s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c m t) x) ≤
      -z ^ 2 + (2 * K + 3 * D1) * w ^ 2 + D1 + T0 ^ 2 := by
    nlinarith only [hdiffScaled, (abs_le.mp hr').1, (abs_le.mp hpair).2,
      sq_nonneg (z - T0), mul_nonneg hD1 (sq_nonneg (w - 1))]
  nlinarith only [hraw, hK, hD1, sq_nonneg T0,
    mul_nonneg (add_nonneg hD1 (sq_nonneg T0)) (sq_nonneg w)]

end PoincareConjecture
