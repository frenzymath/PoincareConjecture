import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Real




theorem exists_quadratic_component_tolerance {K : ℝ} (hK : 1 < K) :
    ∃ d : ℝ, d ∈ Ioo 0 (1 / 2) ∧
      K⁻¹ ^ 2 < (1 - d) ^ 3 / (1 + d) - d ^ 2 / 2 ∧
      (1 + d) ^ 3 / (1 - d) < K ^ 2 := by
  let U : ℝ → ℝ := fun d => (1 + d) ^ 3 / (1 - d)
  let D : ℝ → ℝ := fun d => (1 - d) ^ 3 / (1 + d) - d ^ 2 / 2
  have hU : ContinuousAt U 0 := by
    dsimp only [U]
    fun_prop (disch := norm_num)
  have hD : ContinuousAt D 0 := by
    dsimp only [D]
    fun_prop (disch := norm_num)
  have hkpos : 0 < K := zero_lt_one.trans hK
  have hi : 0 < K⁻¹ := inv_pos.mpr hkpos
  have hi' : K⁻¹ < 1 := inv_lt_one_of_one_lt₀ hK
  have hupper : ∀ᶠ d in 𝓝 (0 : ℝ), U d < K ^ 2 :=
    hU.eventually_lt continuousAt_const (by dsimp [U]; nlinarith)
  have hlower : ∀ᶠ d in 𝓝 (0 : ℝ), K⁻¹ ^ 2 < D d :=
    continuousAt_const.eventually_lt hD (by dsimp [D]; nlinarith)
  have hhalf : ∀ᶠ d in 𝓝 (0 : ℝ), d < 1 / 2 := gt_mem_nhds (by norm_num)
  have he : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      0 < d ∧ d < 1 / 2 ∧ K⁻¹ ^ 2 < D d ∧ U d < K ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hhalf.filter_mono nhdsWithin_le_nhds,
      hlower.filter_mono nhdsWithin_le_nhds, hupper.filter_mono nhdsWithin_le_nhds]
      with d hd hhalf' hlow hup
    exact ⟨hd, hhalf', hlow, hup⟩
  obtain ⟨d, hd, hhalf', hlo, hup⟩ := he.exists
  exact ⟨d, ⟨hd, hhalf'⟩, hlo, hup⟩




theorem quadratic_component_sq_bounds
    {d e e' r V W t a b : ℝ} (hd : d ∈ Ioo 0 (1 / 2))
    (he : e ≤ d) (he' : e' ≤ d) (hr : r ∈ Icc (1 - d) (1 + d))
    (hV : 0 ≤ V)
    (ha : |a - 2 * V ^ 2| ≤ e * (2 * V ^ 2))
    (hb : |b - (2 * W ^ 2 + t ^ 2)| ≤ e' * (2 * W ^ 2 + t ^ 2))
    (hmetric : b = r ^ 2 * a) (ht : |t| ≤ d * V) :
    ((1 - d) ^ 3 / (1 + d) - d ^ 2 / 2) * V ^ 2 ≤ W ^ 2 ∧
      W ^ 2 ≤ ((1 + d) ^ 3 / (1 - d)) * V ^ 2 := by
  have hdm : 0 < 1 - d := by linarith [hd.2]
  have hdp : 0 < 1 + d := by linarith [hd.1]
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hrL : (1 - d) ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hdm.le hr0).mpr hr.1
  have hrU : r ^ 2 ≤ (1 + d) ^ 2 := (sq_le_sq₀ hr0 hdp.le).mpr hr.2
  have haL : (1 - d) * (2 * V ^ 2) ≤ a := by
    have h := mul_le_mul_of_nonneg_right he (sq_nonneg V)
    nlinarith [(abs_le.mp ha).1]
  have haU : a ≤ (1 + d) * (2 * V ^ 2) := by
    have h := mul_le_mul_of_nonneg_right he (sq_nonneg V)
    nlinarith [(abs_le.mp ha).2]
  have ha0 : 0 ≤ a := (mul_nonneg hdm.le (by positivity)).trans haL
  have hbL : (1 - d) * (2 * W ^ 2 + t ^ 2) ≤ b := by
    have h := mul_le_mul_of_nonneg_right he' (by positivity : 0 ≤ 2 * W ^ 2 + t ^ 2)
    nlinarith [(abs_le.mp hb).1]
  have hbU : b ≤ (1 + d) * (2 * W ^ 2 + t ^ 2) := by
    have h := mul_le_mul_of_nonneg_right he' (by positivity : 0 ≤ 2 * W ^ 2 + t ^ 2)
    nlinarith [(abs_le.mp hb).2]
  have hbrL : (1 - d) ^ 3 * (2 * V ^ 2) ≤ b := by
    rw [hmetric]
    calc
      _ = (1 - d) ^ 2 * ((1 - d) * (2 * V ^ 2)) := by ring
      _ ≤ r ^ 2 * a := mul_le_mul hrL haL (by positivity) (sq_nonneg r)
  have hbrU : b ≤ (1 + d) ^ 3 * (2 * V ^ 2) := by
    rw [hmetric]
    calc
      r ^ 2 * a ≤ (1 + d) ^ 2 * ((1 + d) * (2 * V ^ 2)) :=
        mul_le_mul hrU haU ha0 (sq_nonneg _)
      _ = _ := by ring
  have ht2 : t ^ 2 ≤ d ^ 2 * V ^ 2 := by
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg t) (mul_nonneg hd.1.le hV)).mpr ht
  have hfrac : ((1 - d) ^ 3 / (1 + d)) * (2 * V ^ 2) ≤ 2 * W ^ 2 + t ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hdp).mpr
    exact (hbrL.trans hbU).trans_eq (mul_comm _ _)
  refine ⟨by nlinarith, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdm).mpr
  have h := hbL.trans hbrU
  nlinarith [mul_nonneg hdm.le (sq_nonneg t)]




theorem quadratic_component_norm_bounds
    {K d e e' r V W t a b : ℝ} (hK : 1 < K) (hd : d ∈ Ioo 0 (1 / 2))
    (hlo : K⁻¹ ^ 2 < (1 - d) ^ 3 / (1 + d) - d ^ 2 / 2)
    (hup : (1 + d) ^ 3 / (1 - d) < K ^ 2)
    (he : e ≤ d) (he' : e' ≤ d) (hr : r ∈ Icc (1 - d) (1 + d))
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (ha : |a - 2 * V ^ 2| ≤ e * (2 * V ^ 2))
    (hb : |b - (2 * W ^ 2 + t ^ 2)| ≤ e' * (2 * W ^ 2 + t ^ 2))
    (hmetric : b = r ^ 2 * a) (ht : |t| ≤ d * V) :
    K⁻¹ * V ≤ W ∧ W ≤ K * V := by
  have hkpos : 0 < K := zero_lt_one.trans hK
  obtain ⟨hL, hU⟩ := quadratic_component_sq_bounds hd he he' hr hV ha hb hmetric ht
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr hkpos.le) hV) hW).mp
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hlo.le (sq_nonneg V)).trans hL
  · apply (sq_le_sq₀ hW (mul_nonneg hkpos.le hV)).mp
    rw [mul_pow]
    exact hU.trans (mul_le_mul_of_nonneg_right hup.le (sq_nonneg V))

end Real
