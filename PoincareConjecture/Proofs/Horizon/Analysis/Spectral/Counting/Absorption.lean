import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic








namespace Poincare.Analysis.Spectral.Counting

theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (Real.sqrt x) ^ n = x ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring



theorem le_rpow_of_le_error_add_inverse_pow {N A B w : ℝ} (n : ℕ)
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hw : 1 ≤ w)
    (hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      N ≤ A * ε ^ 2 * w * N + B / ε ^ n) :
    N ≤ (2 * B * (2 * (A + 1)) ^ ((n : ℝ) / 2)) * w ^ ((n : ℝ) / 2) := by
  let r : ℝ := Real.sqrt (2 * (A + 1) * w)
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hx : 0 < 2 * (A + 1) * w := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hrsq : r ^ 2 = 2 * (A + 1) * w := Real.sq_sqrt hx.le
  have hrone : 1 ≤ r := by
    have : 1 ≤ 2 * (A + 1) * w := by nlinarith
    dsimp [r]
    exact (Real.le_sqrt (by norm_num) hx.le).mpr (by simpa using this)
  have he : 0 < r⁻¹ := inv_pos.mpr hr
  have heone : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hrone
  have herr : A * (r⁻¹) ^ 2 * w ≤ 1 / 2 := by
    rw [inv_pow, ← div_eq_mul_inv, div_mul_eq_mul_div, hrsq]
    apply (div_le_iff₀ hx).mpr
    nlinarith
  have hb := hbound r⁻¹ he heone
  have hn : N ≤ 2 * B * r ^ n := by
    have heN := mul_le_mul_of_nonneg_right herr hN
    simp only [inv_pow, div_inv_eq_mul] at hb heN
    nlinarith
  refine hn.trans_eq ?_
  dsimp [r]
  rw [sqrt_pow_eq_rpow hx.le,
    Real.mul_rpow (by positivity : 0 ≤ 2 * (A + 1)) hwpos.le]
  ring



theorem one_le_four_mul_weighted_sq_sum {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) (h : 1 / 2 ≤ ∑ i ∈ s, a i * b i) :
    1 ≤ 4 * (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s a b
  nlinarith

theorem norm_sq_le_two_mul_sub_sq_add (K : Type*) [SeminormedAddCommGroup K]
    (x y : K) : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h' : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
  nlinarith [sq_nonneg (‖x - y‖ - ‖y‖), norm_nonneg (x - y), norm_nonneg x,
    norm_nonneg y]



theorem card_le_error_add_trace {ι J K : Type*} [Fintype J]
    [SeminormedAddCommGroup K] (s : Finset ι) (v z : ι → J → K)
    {C A B : ℝ} (hC : 0 ≤ C)
    (hrec : ∀ i ∈ s, 1 ≤ C * ∑ j, ‖v i j‖ ^ 2)
    (herr : ∀ i ∈ s, ∑ j, ‖v i j - z i j‖ ^ 2 ≤ A)
    (htrace : ∑ j, ∑ i ∈ s, ‖z i j‖ ^ 2 ≤ B) :
    (s.card : ℝ) ≤ 2 * C * A * s.card + 2 * C * B := by
  have hpoint (i : ι) (hi : i ∈ s) :
      1 ≤ 2 * C * A + 2 * C * ∑ j, ‖z i j‖ ^ 2 := by
    have hb := Finset.sum_le_sum (s := Finset.univ) fun j hj =>
      norm_sq_le_two_mul_sub_sq_add K (v i j) (z i j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hb
    have h := (hrec i hi).trans (mul_le_mul_of_nonneg_left hb hC)
    have he := mul_le_mul_of_nonneg_left (herr i hi) (by positivity : 0 ≤ 2 * C)
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  have ht := mul_le_mul_of_nonneg_left htrace (by positivity : 0 ≤ 2 * C)
  nlinarith


theorem finite_ncard_le_of_finset_card_le {ι : Type*} (S : Set ι) {C : ℝ}
    (h : ∀ s : Finset ι, (↑s : Set ι) ⊆ S → (s.card : ℝ) ≤ C) :
    S.Finite ∧ (S.ncard : ℝ) ≤ C := by
  classical
  have hfin : S.Finite := by
    by_contra hfin
    obtain ⟨n, hn⟩ := exists_nat_gt C
    obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin n
    have hb := h s hs
    rw [hcard] at hb
    exact (not_le_of_gt hn) hb
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact h hfin.toFinset (by simp)

end Poincare.Analysis.Spectral.Counting
