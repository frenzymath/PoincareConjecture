import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetTangential
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetExpressionBounds

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63Normalization_arc_iterate_bounds [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m : ℕ) (hm : 2 ≤ m)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hLower : ∀ i, i < m →
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c i t x) ≤ L)
    (hRic : ∀ d, d ≤ m + 1 →
      ∀ v : Fin (2 + d) → TangentSpace (𝓡 n) (c x t),
        (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
          |(F.connection t).iteratedCovariantTensorDerivative
            (F.connection t).ricciEvaluation d (c x t) v| ≤ K) :
    let A := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
    let Aj := fun j => ((m62ArcDerivative F c t)^[j]) A x
    let w := (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c m t x)
    let D0 := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3) +
      (2 : ℝ) ^ (m + 1) * L ^ 2
    (∀ j, j < m → |Aj j| ≤ D0) ∧
      |Aj m| ≤ D0 * (1 + w) ∧
      |Aj (m + 1) - 2 * (F.metric t).inner (c x t)
        (m63CurvatureJet F c 0 t x) (m63CurvatureJet F c (m + 1) t x)| ≤
          D0 * (1 + w) := by
  classical
  let g := F.metric t
  let p := c x t
  let J := m63CurvatureJet F c
  let P := fun i j => g.inner p (J i t x) (J j t x)
  let N := fun i => g.tangentNorm p (J i t x)
  let w := N m
  let r := m62TangentRicci F c t
  let q := m62CurvatureSquared F c t
  let A := fun y => r y + q y
  let B := (Nat.factorial (m + 3) : ℝ) * K * L ^ (m + 3)
  let U := (2 : ℝ) ^ (m + 1) * L ^ 2
  have hN (i : ℕ) : 0 ≤ N i := Real.sqrt_nonneg _
  have hw : 0 ≤ w := hN m
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hK) (pow_nonneg hL0 _)
  have hBmul : B ≤ B * (1 + w) := by
    nlinarith only [mul_nonneg hB hw]
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg L
  have hL_le_sq : L ≤ L ^ 2 := by nlinarith only [hL]
  have hLw : L * w ≤ L ^ 2 * (1 + w) := by
    calc
      _ ≤ L ^ 2 * w := mul_le_mul_of_nonneg_right hL_le_sq hw
      _ ≤ L ^ 2 * (1 + w) := by nlinarith only [hLsq]
  have hLsqmul : L ^ 2 ≤ L ^ 2 * (1 + w) := by
    nlinarith only [mul_nonneg hLsq hw]
  have hinner (i j : ℕ) : |P i j| ≤ N i * N j := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    change |inner ℝ (J i t x) (J j t x)| ≤ _
    simpa only [hn] using abs_real_inner_le_norm (J i t x) (J j t x)
  have hpairLow (i j : ℕ) (hi : i < m) (hj : j < m) : |P i j| ≤ L ^ 2 := by
    have hmul := mul_le_mul (hLower i hi) (hLower j hj) (hN j) hL0
    exact (hinner i j).trans (by simpa only [pow_two] using hmul)
  have hpairTop (i j : ℕ) (hi : i ≤ m) (hj : j ≤ m)
      (hnot : ¬(i = m ∧ j = m)) : |P i j| ≤ L ^ 2 * (1 + w) := by
    by_cases him : i = m
    · subst i
      have hjm : j < m := by omega
      calc
        _ ≤ w * N j := hinner m j
        _ ≤ w * L := mul_le_mul_of_nonneg_left (hLower j hjm) hw
        _ = L * w := mul_comm _ _
        _ ≤ _ := hLw
    · by_cases hjm : j = m
      · subst j
        calc
          _ ≤ N i * w := hinner i m
          _ ≤ L * w := mul_le_mul_of_nonneg_right (hLower i (by omega)) hw
          _ ≤ _ := hLw
      · exact (hpairLow i j (by omega) (by omega)).trans hLsqmul
  have hpair (j : ℕ) :
      ((m62ArcDerivative F c t)^[j]) q x =
        ∑ z ∈ Finset.antidiagonal j, (j.choose z.1 : ℝ) * P z.1 z.2 := by
    have h := m63TangentJetPair_arc_iterate F c hc 1 1 j ht x
    dsimp only at h
    have hqfun : q = fun y => (F.metric t).inner (c y t)
        (m62CurvatureVector F c t y) (m62CurvatureVector F c t y) := rfl
    rw [hqfun]
    simpa only [Nat.add_comm 1, m63CurvatureJet,
      P, J, g, p] using h
  have hmass (j : ℕ) :
      (∑ z ∈ Finset.antidiagonal j, (j.choose z.1 : ℝ)) = (2 : ℝ) ^ j := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact_mod_cast Nat.sum_range_choose j
  have hsum (j : ℕ) (S : Finset (ℕ × ℕ)) (hS : S ⊆ Finset.antidiagonal j)
      (C : ℝ) (hC : 0 ≤ C) (hp : ∀ z ∈ S, |P z.1 z.2| ≤ C) :
      |∑ z ∈ S, (j.choose z.1 : ℝ) * P z.1 z.2| ≤ (2 : ℝ) ^ j * C := by
    calc
      _ ≤ ∑ z ∈ S, |(j.choose z.1 : ℝ) * P z.1 z.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ S, (j.choose z.1 : ℝ) * C := by
        apply Finset.sum_le_sum
        intro z hz
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hp z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ S, (j.choose z.1 : ℝ)) * C := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ z ∈ Finset.antidiagonal j, (j.choose z.1 : ℝ)) * C :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg hS (fun z _ _ => Nat.cast_nonneg _)) hC
      _ = (2 : ℝ) ^ j * C := by rw [hmass]
  have hqLow (j : ℕ) (hj : j < m) :
      |((m62ArcDerivative F c t)^[j]) q x| ≤ U := by
    rw [hpair]
    have hb := hsum j (Finset.antidiagonal j) (fun _ hz => hz) (L ^ 2) hLsq (by
      intro z hz
      have h := Finset.mem_antidiagonal.mp hz
      exact hpairLow z.1 z.2 (by omega) (by omega))
    exact hb.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hLsq)
  have hqTop : |((m62ArcDerivative F c t)^[m]) q x| ≤ U * (1 + w) := by
    rw [hpair]
    have hb := hsum m (Finset.antidiagonal m) (fun _ hz => hz)
      (L ^ 2 * (1 + w)) (mul_nonneg hLsq (by positivity)) (by
        intro z hz
        have h := Finset.mem_antidiagonal.mp hz
        exact hpairTop z.1 z.2 (by omega) (by omega) (by omega))
    have hpow : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (hb.trans (mul_le_mul_of_nonneg_right hpow
      (mul_nonneg hLsq (by positivity)))).trans_eq (by dsimp only [U]; ring)
  have hqNext : |((m62ArcDerivative F c t)^[m + 1]) q x -
      2 * P 0 (m + 1)| ≤ U * (1 + w) := by
    let S := Finset.antidiagonal (m + 1)
    let e0 : ℕ × ℕ := (0, m + 1)
    let e1 : ℕ × ℕ := (m + 1, 0)
    let f := fun z : ℕ × ℕ => ((m + 1).choose z.1 : ℝ) * P z.1 z.2
    have he0 : e0 ∈ S := by simp only [S, e0, Finset.mem_antidiagonal, zero_add]
    have he1 : e1 ∈ S.erase e0 := by
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro h
        have hfst := congrArg Prod.fst h
        dsimp only [e0, e1] at hfst
        omega
      · simp only [S, e1, Finset.mem_antidiagonal, add_zero]
    have hzero := Finset.sum_erase_add S f he0
    have hlast := Finset.sum_erase_add (S.erase e0) f he1
    have hf0 : f e0 = P 0 (m + 1) := by
      simp only [f, e0, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have hf1 : f e1 = P (m + 1) 0 := by
      simp only [f, e1, Nat.choose_self, Nat.cast_one, one_mul]
    rw [hf0] at hzero
    rw [hf1] at hlast
    have hsym : P (m + 1) 0 = P 0 (m + 1) := g.symm p _ _
    have heq : (∑ z ∈ S, f z) - 2 * P 0 (m + 1) =
        ∑ z ∈ (S.erase e0).erase e1, f z := by
      linarith only [hzero, hlast, hsym]
    rw [hpair]
    change |(∑ z ∈ S, f z) - 2 * P 0 (m + 1)| ≤ _
    rw [heq]
    have hb := hsum (m + 1) ((S.erase e0).erase e1)
      (fun _ hz => (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2)
      (L ^ 2 * (1 + w)) (mul_nonneg hLsq (by positivity)) (by
        intro z hz
        have hz1 := Finset.mem_erase.mp hz
        have hz0 := Finset.mem_erase.mp hz1.2
        have hdiag := Finset.mem_antidiagonal.mp hz0.2
        have hzfst : z.1 ≠ 0 := by
          intro h
          apply hz0.1
          apply Prod.ext h
          dsimp only [e0]
          omega
        have hzsnd : z.2 ≠ 0 := by
          intro h
          apply hz1.1
          apply Prod.ext
          · dsimp only [e1]
            omega
          · exact h
        exact hpairTop z.1 z.2 (by omega) (by omega) (by omega))
    exact hb.trans_eq (by dsimp only [U]; ring)
  have hA : ContDiff ℝ ∞ A :=
    (normalization_coefficient_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hq : ContDiff ℝ ∞ q :=
    (curvatureSquared_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hr : ContDiff ℝ ∞ r := by
    have heq : (fun y => A y - q y) = r := by
      funext y
      dsimp only [A]
      ring
    have h := hA.sub hq
    rwa [heq] at h
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hvi := hv.inv (fun y => (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne')
  have hsmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) :
      ContDiff ℝ ∞ (((m62ArcDerivative F c t)^[j]) f) := by
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hvi.mul (contDiff_infty_iff_deriv.mp ih).2
  have hsplit (j : ℕ) : ((m62ArcDerivative F c t)^[j]) A =
      fun y => ((m62ArcDerivative F c t)^[j]) r y +
        ((m62ArcDerivative F c t)^[j]) q y := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      funext y
      have hd := (((hsmooth r hr j).differentiable (by simp) y).hasDerivAt).fun_add
        (((hsmooth q hq j).differentiable (by simp) y).hasDerivAt)
      rw [m62ArcDerivative, hd.deriv]
      simp only [Function.iterate_succ_apply', m62ArcDerivative]
      ring
  have hRicIter := m63TangentRicci_arc_iterate_abs_le F c hc m hK hL ht x hLower hRic
  change (∀ j, j ≤ m → |((m62ArcDerivative F c t)^[j]) r x| ≤ B) ∧
    |((m62ArcDerivative F c t)^[m + 1]) r x| ≤ B * (1 + w) at hRicIter
  change (∀ j, j < m → |((m62ArcDerivative F c t)^[j]) A x| ≤ B + U) ∧
    |((m62ArcDerivative F c t)^[m]) A x| ≤ (B + U) * (1 + w) ∧
    |((m62ArcDerivative F c t)^[m + 1]) A x - 2 * P 0 (m + 1)| ≤
      (B + U) * (1 + w)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add (hRicIter.1 j (by omega)) (hqLow j hj))
  · rw [hsplit]
    exact ((abs_add_le _ _).trans
      (add_le_add ((hRicIter.1 m le_rfl).trans hBmul) hqTop)).trans_eq (by ring)
  · rw [hsplit]
    rw [show ((m62ArcDerivative F c t)^[m + 1]) r x +
        ((m62ArcDerivative F c t)^[m + 1]) q x - 2 * P 0 (m + 1) =
      ((m62ArcDerivative F c t)^[m + 1]) r x +
        (((m62ArcDerivative F c t)^[m + 1]) q x - 2 * P 0 (m + 1)) by ring]
    exact ((abs_add_le _ _).trans (add_le_add hRicIter.2 hqNext)).trans_eq (by ring)

end PoincareConjecture
