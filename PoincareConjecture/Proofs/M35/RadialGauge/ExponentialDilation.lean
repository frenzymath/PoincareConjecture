import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false

open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem linear_positive_jet_bound (L : E →L[ℝ] F) (j : ℕ) (hj : 1 ≤ j)
    (x : E) : ‖iteratedFDeriv ℝ j L x‖ ≤ ‖L‖ := by
  cases j with
  | zero => omega
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hd : fderiv ℝ L = fun _ => L := funext (fun x => L.hasFDerivAt.fderiv)
      rw [hd]
      cases j with
      | zero => rw [norm_iteratedFDeriv_zero]
      | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, norm_nonneg]

private theorem exp_snd_jet_bound (j : ℕ) (p : E × ℝ) :
    ‖iteratedFDeriv ℝ j (fun q : E × ℝ => Real.exp q.2) p‖ ≤
      (j.factorial : ℝ) * Real.exp p.2 := by
  have h := norm_iteratedFDeriv_comp_le Real.contDiff_exp
    (contDiff_snd : ContDiff ℝ ∞ (fun q : E × ℝ => q.2))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j) p
    (C := Real.exp p.2) (D := 1) ?_ ?_
  · simpa only [Function.comp_def, one_pow, mul_one] using h
  · intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have he : iteratedDeriv i Real.exp = Real.exp := by
      simpa only [one_mul, one_pow] using iteratedDeriv_exp_const_mul i 1
    rw [he, Real.abs_exp]
  · intro i hi _
    rw [one_pow]
    exact (linear_positive_jet_bound (ContinuousLinearMap.snd ℝ E ℝ) i hi p).trans
      (ContinuousLinearMap.norm_snd_le ℝ E ℝ)

theorem exponential_dilation_jet_bound (eta : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ∀ sigma : ℝ, |sigma| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : E × ℝ => Real.exp p.2 • p.1) (x, sigma)‖ ≤
        C * (1 + ‖x‖) := by
  classical
  let C := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * (i.factorial : ℝ) * Real.exp eta
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨C + 1, by positivity, ?_⟩
  intro x sigma hsigma
  have hf (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun p : E × ℝ => p.1) (x, sigma)‖ ≤ 1 + ‖x‖ := by
    cases i with
    | zero => simpa only [norm_iteratedFDeriv_zero] using le_add_of_nonneg_left zero_le_one
    | succ i =>
        exact ((linear_positive_jet_bound (ContinuousLinearMap.fst ℝ E ℝ) (i + 1)
          (by omega) (x, sigma)).trans (ContinuousLinearMap.norm_fst_le ℝ E ℝ)).trans
            (le_add_of_nonneg_right (norm_nonneg x))
  have he (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun p : E × ℝ => Real.exp p.2) (x, sigma)‖ ≤
        (i.factorial : ℝ) * Real.exp eta :=
    (exp_snd_jet_bound i (x, sigma)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self sigma).trans hsigma))
        (Nat.cast_nonneg _))
  have h := norm_iteratedFDeriv_smul_le
    (contDiff_snd.exp : ContDiff ℝ ∞ (fun p : E × ℝ => Real.exp p.2))
    (contDiff_fst : ContDiff ℝ ∞ (fun p : E × ℝ => p.1))
    (x, sigma) (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  apply h.trans
  calc
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun p : E × ℝ => Real.exp p.2) (x, sigma)‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun p : E × ℝ => p.1) (x, sigma)‖
        ≤ ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * (i.factorial : ℝ) * Real.exp eta) * (1 + ‖x‖) := by
      apply Finset.sum_le_sum
      intro i _
      have hm := mul_le_mul
        (mul_le_mul_of_nonneg_left (he i) (Nat.cast_nonneg (j.choose i)))
        (hf (j - i)) (norm_nonneg _) (by positivity)
      simpa only [mul_assoc] using hm
    _ = C * (1 + ‖x‖) := by rw [← Finset.sum_mul]
    _ ≤ (C + 1) * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end PoincareConjecture.M35.RadialGauge
