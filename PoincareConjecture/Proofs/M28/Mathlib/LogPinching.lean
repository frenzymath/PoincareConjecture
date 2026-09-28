import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Real

open Filter
open scoped Topology

theorem lt_mul_of_log_pinching {R v Q eta B : ℝ}
    (heta : 0 < eta) (hB : 0 ≤ B)
    (hQ : exp (3 + (B + 1) / (2 * eta)) / eta ≤ Q)
    (hR : R ≤ B * Q)
    (hpinch : 0 < v → 2 * v * (log v - 3) ≤ R) :
    v < eta * Q := by
  by_contra h
  have hv : eta * Q ≤ v := le_of_not_gt h
  have hQpos : 0 < Q :=
    lt_of_lt_of_le (div_pos (exp_pos _) heta) hQ
  have hvpos : 0 < v := lt_of_lt_of_le (mul_pos heta hQpos) hv
  have hexp : exp (3 + (B + 1) / (2 * eta)) ≤ v := by
    calc
      exp (3 + (B + 1) / (2 * eta)) ≤ Q * eta := (div_le_iff₀ heta).mp hQ
      _ = eta * Q := mul_comm _ _
      _ ≤ v := hv
  have hlog := log_le_log (exp_pos _) hexp
  rw [log_exp] at hlog
  have hden : 0 < 2 * eta := by positivity
  have hlogbound : B + 1 ≤ (log v - 3) * (2 * eta) :=
    (div_le_iff₀ hden).mp (by linarith)
  have hlognonneg : 0 ≤ log v - 3 := by
    have : 0 ≤ (B + 1) / (2 * eta) := by positivity
    linarith
  have hpinch' := hpinch hvpos
  have hreplace := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)) hlognonneg
  have hscaled := mul_le_mul_of_nonneg_right hlogbound hQpos.le
  nlinarith

theorem tendsto_zero_of_log_pinching {α : Type*} {l : Filter α}
    {R v Q : α → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : Tendsto Q l atTop)
    (hv : ∀ᶠ k in l, 0 ≤ v k)
    (hR : ∀ᶠ k in l, R k ≤ B * Q k)
    (hpinch : ∀ᶠ k in l, 0 < v k → 2 * v k * (log (v k) - 3) ≤ R k) :
    Tendsto (fun k ↦ v k / Q k) l (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hQ.eventually_gt_atTop 0, hv] with k hkQ hkv
    exact ha.trans_le (div_nonneg hkv hkQ.le)
  · intro eta heta
    filter_upwards [hQ.eventually_ge_atTop (exp (3 + (B + 1) / (2 * eta)) / eta),
      hQ.eventually_gt_atTop 0, hR, hpinch] with k hkQ hkQpos hkR hkpinch
    exact (div_lt_iff₀ hkQpos).mpr (lt_mul_of_log_pinching heta hB hkQ hkR hkpinch)

end Real
