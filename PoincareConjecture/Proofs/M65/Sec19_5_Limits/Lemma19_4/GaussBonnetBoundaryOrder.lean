import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M65Gauss

theorem even_order_of_monotone_derivative {f q : ℝ → ℝ} {m : ℕ}
    (hmono : Monotone f ∨ Antitone f) (hq : ContinuousAt q 0) (hq0 : q 0 ≠ 0)
    (hfactor : ∀ᶠ x in 𝓝 (0 : ℝ), deriv f x = x ^ m * q x) : Even m := by
  by_contra hn
  have hodd : Odd m := Nat.not_even_iff_odd.mp hn
  have hnc : ContinuousAt (fun x : ℝ => -x) 0 := continuous_neg.continuousAt
  have hc : ContinuousAt (fun x : ℝ => q x * q (-x)) 0 :=
    hq.mul (hq.comp_of_eq hnc (neg_zero : -(0 : ℝ) = 0))
  have hp : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < q x * q (-x) :=
    hc.eventually (lt_mem_nhds (by simpa using mul_self_pos.mpr hq0))
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, neg_zero] using hnc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hp.and (hfactor.and (hneg.eventually hfactor)))
  let x := r / 2
  have hx : 0 < x := half_pos hr
  have hxr : dist x 0 < r := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hx]
    exact half_lt_self hr
  obtain ⟨hqq, hplus, hminus⟩ := hball hxr
  have hsame : 0 ≤ deriv f x * deriv f (-x) := by
    rcases hmono with hm | hm
    · exact mul_nonneg (hm.deriv_nonneg) (hm.deriv_nonneg)
    · exact mul_nonneg_of_nonpos_of_nonpos (hm.deriv_nonpos) (hm.deriv_nonpos)
  have hbad : deriv f x * deriv f (-x) < 0 := by
    rw [hplus, hminus, hodd.neg_pow]
    calc
      x ^ m * q x * (-(x ^ m) * q (-x)) = -(x ^ m) ^ 2 * (q x * q (-x)) := by ring
      _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos (pow_pos hx m) 2)) hqq
  exact (not_lt_of_ge hsame) hbad

end PoincareConjecture.M65Gauss
