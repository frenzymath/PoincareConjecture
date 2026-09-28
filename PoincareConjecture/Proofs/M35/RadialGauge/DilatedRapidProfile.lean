import PoincareConjecture.Proofs.M35.RadialGauge.ExponentialDilation










set_option autoImplicit false

open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

variable {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem dilated_rapid_profile_jets_bounded {f : A → E → F} {eta : ℝ}
    (heta : 0 ≤ eta) (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hrapid : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x,
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ a x sigma, |sigma| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : E × ℝ => f a (Real.exp p.2 • p.1)) (x, sigma)‖ ≤ C := by
  classical
  intro k
  choose B hB0 hB using fun j => hrapid j k
  choose D hD0 hD using fun j => exponential_dilation_jet_bound (E := E) eta j
  let B' := 1 + ∑ i ∈ Finset.range (k + 1), B i
  let D' := 1 + ∑ i ∈ Finset.range (k + 1), D i
  let q := Real.exp (-eta)
  have hB' : 0 < B' := by
    have := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun i _ => hB0 i)
    dsimp only [B']
    linarith
  have hD' : 1 ≤ D' := by
    have := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun i _ => (hD0 i).le)
    dsimp only [D']
    linarith
  have hq : 0 < q := Real.exp_pos _
  have hqone : q ≤ 1 := by
    simpa only [q, Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr heta)
  let C := (k.factorial : ℝ) * B' * (D' / q) ^ k
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C + 1, by positivity, ?_⟩
  intro a x sigma hsigma
  let w := 1 + ‖x‖
  have hw : 1 ≤ w := le_add_of_nonneg_right (norm_nonneg x)
  have hwp : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hscale : q * w ≤ 1 + ‖Real.exp sigma • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    have hqexp : q ≤ Real.exp sigma := Real.exp_le_exp.mpr (neg_le_of_abs_le hsigma)
    have hm := mul_le_mul_of_nonneg_right hqexp (norm_nonneg x)
    dsimp only [w]
    nlinarith only [hm, hqone]
  have houter (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (f a) (Real.exp sigma • x)‖ ≤ B' / (q * w) ^ k := by
    apply (le_div_iff₀ (pow_pos (mul_pos hq hwp) k)).mpr
    have hBi : B i ≤ B' := by
      have hh := Finset.single_le_sum (f := B) (fun i _ => hB0 i)
        (show i ∈ Finset.range (k + 1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hi)
      dsimp only [B']
      linarith
    have hweight := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_pos hq hwp).le hscale k)
      (norm_nonneg (iteratedFDeriv ℝ i (f a) (Real.exp sigma • x)))
    have hweight' : ‖iteratedFDeriv ℝ i (f a) (Real.exp sigma • x)‖ * (q * w) ^ k ≤
        (1 + ‖Real.exp sigma • x‖) ^ k *
          ‖iteratedFDeriv ℝ i (f a) (Real.exp sigma • x)‖ := by
      simpa only [mul_comm] using hweight
    exact hweight'.trans ((hB i a _).trans hBi)
  have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun p : E × ℝ => Real.exp p.2 • p.1) (x, sigma)‖ ≤
        (D' * w) ^ i := by
    have hDi : D i ≤ D' := by
      have hh := Finset.single_le_sum (f := D) (fun i _ => (hD0 i).le)
        (show i ∈ Finset.range (k + 1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hik)
      dsimp only [D']
      linarith
    have hbase : 1 ≤ D' * w := hw.trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD' hwp.le)
    exact ((hD i x sigma hsigma).trans
      (mul_le_mul_of_nonneg_right hDi hwp.le)).trans
        (le_self_pow₀ hbase (by omega))
  have hcomp := norm_iteratedFDeriv_comp_le (hf a)
    (contDiff_snd.exp.smul contDiff_fst :
      ContDiff ℝ ∞ (fun p : E × ℝ => Real.exp p.2 • p.1))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) (x, sigma) houter hinner
  have hid : (k.factorial : ℝ) * (B' / (q * w) ^ k) * (D' * w) ^ k = C := by
    dsimp only [C]
    simp only [mul_pow, div_pow]
    field_simp [hq.ne', hwp.ne']
  exact (hcomp.trans_eq hid).trans (by linarith)

end PoincareConjecture.M35.RadialGauge
