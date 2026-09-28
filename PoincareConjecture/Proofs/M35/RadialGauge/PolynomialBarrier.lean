import PoincareConjecture.Proofs.M35.RadialGauge.HalfLineMaximum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

noncomputable def polynomialBarrier (N A L t r : ℝ) : ℝ :=
  A * Real.exp (L * t - N * Real.log (1 + r ^ 2))

theorem polynomialBarrier_nonneg {N A L t r : ℝ} (hA : 0 ≤ A) :
    0 ≤ polynomialBarrier N A L t r := mul_nonneg hA (Real.exp_nonneg _)

theorem polynomialBarrier_contDiff (N A L t : ℝ) :
    ContDiff ℝ ∞ (polynomialBarrier N A L t) := by
  have hlog : ContDiff ℝ ∞ (fun r : ℝ => Real.log (1 + r ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).log (fun r => by positivity)
  exact contDiff_const.mul ((contDiff_const.sub (contDiff_const.mul hlog)).exp)

theorem polynomialBarrier_hasDerivAt_time (N A L t r : ℝ) :
    HasDerivAt (fun s => polynomialBarrier N A L s r)
      (L * polynomialBarrier N A L t r) t := by
  convert! ((((hasDerivAt_id t).const_mul L).sub_const
    (N * Real.log (1 + r ^ 2))).exp.const_mul A) using 1
  simp only [polynomialBarrier, id_eq, mul_one]
  ring

theorem polynomialBarrier_hasDerivAt (N A L t r : ℝ) :
    HasDerivAt (polynomialBarrier N A L t)
      ((-2 * N * r / (1 + r ^ 2)) * polynomialBarrier N A L t r) r := by
  have hn : 1 + r ^ 2 ≠ 0 := by positivity
  have hlog := (((hasDerivAt_id r).pow 2).const_add 1).log hn
  have h := ((hlog.const_mul N).const_sub (L * t)).exp.const_mul A
  convert! h using 1
  simp only [polynomialBarrier, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  ring

theorem polynomialBarrier_deriv_hasDerivAt (N A L t r : ℝ) :
    HasDerivAt (deriv (polynomialBarrier N A L t))
      ((-2 * N / (1 + r ^ 2) + 4 * N * (N + 1) * r ^ 2 / (1 + r ^ 2) ^ 2) *
        polynomialBarrier N A L t r) r := by
  have hn : 1 + r ^ 2 ≠ 0 := by positivity
  have heq : deriv (polynomialBarrier N A L t) = fun s =>
      (-2 * N * s / (1 + s ^ 2)) * polynomialBarrier N A L t s :=
    funext (fun s => (polynomialBarrier_hasDerivAt N A L t s).deriv)
  rw [heq]
  have ha := ((hasDerivAt_id r).const_mul (-2 * N)).div
    (((hasDerivAt_id r).pow 2).const_add 1) hn
  have h := ha.mul (polynomialBarrier_hasDerivAt N A L t r)
  apply h.congr_deriv
  simp only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, Pi.div_apply]
  field_simp [hn]
  ring

theorem polynomialBarrier_first_bound {N A L t r : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hr : 0 ≤ r) :
    |deriv (polynomialBarrier N A L t) r| ≤ 2 * N * polynomialBarrier N A L t r := by
  have hq := polynomialBarrier_nonneg (N := N) (L := L) (t := t) (r := r) hA
  have hbase : 0 < 1 + r ^ 2 := by positivity
  have hratio : r / (1 + r ^ 2) ≤ 1 := by
    apply (div_le_one hbase).mpr
    nlinarith only [sq_nonneg (r - 1)]
  have hbound := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * N by positivity)
  rw [(polynomialBarrier_hasDerivAt N A L t r).deriv, abs_mul, abs_of_nonneg hq]
  have hcoef : |-2 * N * r / (1 + r ^ 2)| = 2 * N * (r / (1 + r ^ 2)) := by
    have hn : -2 * N * r / (1 + r ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) hN) hr) hbase.le
    rw [abs_of_nonpos hn]
    ring
  rw [hcoef]
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hbound) hq

theorem polynomialBarrier_second_bound {N A L t r : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) :
    deriv (deriv (polynomialBarrier N A L t)) r ≤
      (4 * N * (N + 1)) * polynomialBarrier N A L t r := by
  have hq := polynomialBarrier_nonneg (N := N) (L := L) (t := t) (r := r) hA
  have hbase : 0 < 1 + r ^ 2 := by positivity
  have hratio : r ^ 2 / (1 + r ^ 2) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hbase)).mpr
    nlinarith only [sq_nonneg r, sq_nonneg (r ^ 2)]
  have hbound := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ 4 * N * (N + 1) by positivity)
  have hneg : -2 * N / (1 + r ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) hN) hbase.le
  rw [← mul_div_assoc, mul_one] at hbound
  rw [(polynomialBarrier_deriv_hasDerivAt N A L t r).deriv]
  apply mul_le_mul_of_nonneg_right _ hq
  nlinarith only [hbound, hneg]

theorem polynomialBarrier_supersolution {N A K V t r v c : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hV : 0 ≤ V) (hr : 0 ≤ r)
    (hv : |v| ≤ V) (hc : c ≤ K) :
    deriv (deriv (polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) t)) r -
        v * deriv (polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) t) r +
        c * polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) t r ≤
      (4 * N * (N + 1) + 2 * V * N + K) *
        polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) t r := by
  let L := 4 * N * (N + 1) + 2 * V * N + K
  have hq := polynomialBarrier_nonneg (N := N) (L := L) (t := t) (r := r) hA
  have hfirst := polynomialBarrier_first_bound (L := L) (t := t) hN hA hr
  have hsecond := polynomialBarrier_second_bound (L := L) (t := t) (r := r) hN hA
  have hreaction := mul_le_mul_of_nonneg_right hc hq
  have hdrift : -v * deriv (polynomialBarrier N A L t) r ≤
      V * (2 * N * polynomialBarrier N A L t r) := by
    calc
      _ ≤ |-v * deriv (polynomialBarrier N A L t) r| := le_abs_self _
      _ = |v| * |deriv (polynomialBarrier N A L t) r| := by rw [abs_mul, abs_neg]
      _ ≤ V * (2 * N * polynomialBarrier N A L t r) :=
        mul_le_mul hv hfirst (abs_nonneg _) hV
  change _ ≤ L * polynomialBarrier N A L t r
  dsimp only [L] at *
  nlinarith only [hsecond, hdrift, hreaction]

end PoincareConjecture.M35.RadialGauge
