import PoincareConjecture.Proofs.M35.RadialGauge.PolynomialBarrier

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

theorem halfLine_le_polynomialBarrier
    {p velocity reaction : ℝ → ℝ → ℝ} {T K V M N A : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hV : 0 ≤ V) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hcont : ContinuousOn (Function.uncurry p) (Icc 0 T ×ˢ Ici 0))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (p t))
    (hbound : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, p t r ≤ M)
    (hv : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, |velocity t r| ≤ V)
    (hc : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, reaction t r ≤ K)
    (hinit : ∀ r ≥ 0,
      p 0 r ≤ polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) 0 r)
    (htip : ∀ t ∈ Icc 0 T,
      p t 0 ≤ polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) t 0)
    (hPDE : ∀ t ∈ Ioc 0 T, ∀ r > 0,
      HasDerivWithinAt (fun s => p s r)
        (deriv (deriv (p t)) r - velocity t r * deriv (p t) r + reaction t r * p t r)
        (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      p t r ≤ polynomialBarrier N A (4 * N * (N + 1) + 2 * V * N + K) t r := by
  let L := 4 * N * (N + 1) + 2 * V * N + K
  let q := polynomialBarrier N A L
  let w : ℝ → ℝ → ℝ := fun t r => p t r - q t r
  have hqc : Continuous (Function.uncurry q) := by
    have hpoly : Continuous (fun z : ℝ × ℝ => 1 + z.2 ^ 2) :=
      continuous_const.add (continuous_snd.pow 2)
    have hlog := hpoly.log (fun z => by positivity)
    have harg : Continuous (fun z : ℝ × ℝ => L * z.1 - N * Real.log (1 + z.2 ^ 2)) :=
      (continuous_const.mul continuous_fst).sub (continuous_const.mul hlog)
    exact continuous_const.mul (Real.continuous_exp.comp harg)
  have hws (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (w t) :=
    (hs t ht).sub (polynomialBarrier_contDiff N A L t)
  have hwb (t : ℝ) (ht : t ∈ Icc 0 T) (r : ℝ) (hr : 0 ≤ r) : w t r ≤ M := by
    have hq := polynomialBarrier_nonneg (N := N) (L := L) (t := t) (r := r) hA
    have hp := hbound t ht r hr
    dsimp only [w, q]
    linarith only [hq, hp]
  have hwinit (r : ℝ) (hr : 0 ≤ r) : w 0 r ≤ 0 := sub_nonpos.mpr (hinit r hr)
  have hwtip (t : ℝ) (ht : t ∈ Icc 0 T) : w t 0 ≤ 0 := sub_nonpos.mpr (htip t ht)
  have hwPDE (t : ℝ) (ht : t ∈ Ioc 0 T) (r : ℝ) (hr : 0 < r)
      (hpos : 0 < w t r) :
      ∃ d : ℝ, HasDerivWithinAt (fun s => w s r) d (Icc 0 T) t ∧
        d ≤ deriv (deriv (w t)) r + V * |deriv (w t) r| + K * w t r := by
    have htcc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hps := hs t htcc
    have hqs := polynomialBarrier_contDiff N A L t
    have hfirst (z : ℝ) : deriv (fun y => p t y - q t y) z =
        deriv (p t) z - deriv (q t) z :=
      (((hps.differentiable (by simp) z).hasDerivAt).sub
        ((hqs.differentiable (by simp) z).hasDerivAt)).deriv
    have hfirstFun : deriv (w t) = fun z => deriv (p t) z - deriv (q t) z :=
      funext hfirst
    have hsecond : deriv (deriv (w t)) r =
        deriv (deriv (p t)) r - deriv (deriv (q t)) r := by
      rw [hfirstFun]
      exact ((((contDiff_infty_iff_deriv.mp hps).2.differentiable (by simp) r).hasDerivAt).sub
        (((contDiff_infty_iff_deriv.mp hqs).2.differentiable (by simp) r).hasDerivAt)).deriv
    have hqPDE := polynomialBarrier_supersolution (K := K) (t := t)
      hN hA hV hr.le (hv t htcc r hr.le) (hc t htcc r hr.le)
    have hdrift : -velocity t r * deriv (w t) r ≤ V * |deriv (w t) r| := by
      calc
        _ ≤ |-velocity t r * deriv (w t) r| := le_abs_self _
        _ = |velocity t r| * |deriv (w t) r| := by rw [abs_mul, abs_neg]
        _ ≤ V * |deriv (w t) r| :=
          mul_le_mul_of_nonneg_right (hv t htcc r hr.le) (abs_nonneg _)
    have hreaction := mul_le_mul_of_nonneg_right (hc t htcc r hr.le) hpos.le
    refine ⟨deriv (deriv (p t)) r - velocity t r * deriv (p t) r +
        reaction t r * p t r - L * q t r,
      (hPDE t ht r hr).sub (polynomialBarrier_hasDerivAt_time N A L t r).hasDerivWithinAt, ?_⟩
    rw [hsecond, hfirstFun]
    rw [hfirstFun] at hdrift
    change deriv (deriv (q t)) r - velocity t r * deriv (q t) r +
      reaction t r * q t r ≤ L * q t r at hqPDE
    dsimp only [w] at hreaction ⊢
    nlinarith only [hqPDE, hdrift, hreaction]
  have hcomparison := halfLine_nonpositive_of_bounded (w := w) hT hK hV
    (hcont.sub hqc.continuousOn) hws hwb hwinit hwtip hwPDE
  intro t ht r hr
  exact sub_nonpos.mp (hcomparison t ht r hr)

theorem polynomialBarrier_nat_eq (N : ℕ) (A L t r : ℝ) :
    polynomialBarrier N A L t r = A * Real.exp (L * t) / (1 + r ^ 2) ^ N := by
  unfold polynomialBarrier
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by positivity)]
  ring

theorem halfLine_polynomial_bound_of_initial_support
    {p velocity reaction : ℝ → ℝ → ℝ} {T K V R : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hcont : ContinuousOn (Function.uncurry p) (Icc 0 T ×ˢ Ici 0))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (p t))
    (hbound : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, p t r ≤ 1)
    (hv : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, |velocity t r| ≤ V)
    (hc : ∀ t ∈ Icc 0 T, ∀ r ≥ 0, reaction t r ≤ K)
    (hinit : ∀ r, R ≤ r → p 0 r = 0)
    (hPDE : ∀ t ∈ Ioc 0 T, ∀ r > 0,
      HasDerivWithinAt (fun s => p s r)
        (deriv (deriv (p t)) r - velocity t r * deriv (p t) r + reaction t r * p t r)
        (Icc 0 T) t) :
    ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      (1 + r ^ 2) ^ N * p t r ≤ C := by
  intro N
  let A := (1 + R ^ 2) ^ N
  let L := 4 * (N : ℝ) * (N + 1) + 2 * V * N + K
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAone : 1 ≤ A := one_le_pow₀ (by nlinarith only [sq_nonneg R])
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hstart (r : ℝ) (hr : 0 ≤ r) : p 0 r ≤ polynomialBarrier N A L 0 r := by
    by_cases hlarge : R ≤ r
    · rw [hinit r hlarge]
      exact polynomialBarrier_nonneg hA.le
    · have hrR : r ≤ R := (lt_of_not_ge hlarge).le
      have hbase : (1 + r ^ 2) ^ N ≤ A := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith only [hr, hrR]
      have hqone : 1 ≤ polynomialBarrier N A L 0 r := by
        rw [polynomialBarrier_nat_eq]
        simp only [mul_zero, Real.exp_zero, mul_one]
        exact (one_le_div (by positivity)).mpr hbase
      exact (hbound 0 ⟨le_rfl, hT.le⟩ r hr).trans hqone
  have htip (t : ℝ) (ht : t ∈ Icc 0 T) : p t 0 ≤ polynomialBarrier N A L t 0 := by
    have hexp : 1 ≤ Real.exp (L * t) := Real.one_le_exp_iff.mpr (mul_nonneg hL ht.1)
    have hqone : 1 ≤ polynomialBarrier N A L t 0 := by
      rw [polynomialBarrier_nat_eq]
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, one_pow, div_one] using
        one_le_mul_of_one_le_of_one_le hAone hexp
    exact (hbound t ht 0 le_rfl).trans hqone
  have hcomparison := halfLine_le_polynomialBarrier hT hK hV hN hA.le hcont hs hbound
    hv hc hstart htip hPDE
  refine ⟨A * Real.exp (L * T), mul_pos hA (Real.exp_pos _), ?_⟩
  intro t ht r hr
  have hp := hcomparison t ht r hr
  rw [polynomialBarrier_nat_eq] at hp
  have hscaled := (le_div_iff₀ (show 0 < (1 + r ^ 2) ^ N by positivity)).mp hp
  have hexp : Real.exp (L * t) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hL)
  have htime := mul_le_mul_of_nonneg_left hexp hA.le
  nlinarith only [hscaled, htime]

end PoincareConjecture.M35.RadialGauge
