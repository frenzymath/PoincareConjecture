import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set

namespace PoincareConjecture

theorem m64Morrey_energy_le_power_of_contraction
    {E : ℝ → ℝ} {rho q D : ℝ} (hrho : 0 < rho) (hq : 0 < q) (hq1 : q < 1)
    (hD : 0 ≤ D) (hmono : MonotoneOn E (Ioc 0 rho)) (hbase : E rho ≤ D)
    (hstep : ∀ r ∈ Ioc 0 rho, E (r * Real.exp (-1)) ≤ q * E r)
    {r : ℝ} (hr : r ∈ Ioc 0 rho) :
    E r ≤ (D / (q * rho ^ (-Real.log q))) * r ^ (-Real.log q) := by
  let a := Real.exp (-1)
  let beta := -Real.log q
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hbeta : 0 < beta := neg_pos.mpr (Real.log_neg hq hq1)
  have haq : a ^ beta = q := by
    rw [Real.rpow_def_of_pos ha]
    simp only [a, beta, Real.log_exp, neg_mul_neg, one_mul, Real.exp_log hq]
  have hscale (j : ℕ) : rho * a ^ j ∈ Ioc 0 rho := by
    refine ⟨mul_pos hrho (pow_pos ha _), ?_⟩
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ha.le ha1.le) hrho.le).trans_eq
      (mul_one rho)
  have hiter (j : ℕ) : E (rho * a ^ j) ≤ D * q ^ j := by
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      calc
        E (rho * a ^ (j + 1)) = E ((rho * a ^ j) * Real.exp (-1)) := by
          rw [pow_succ, mul_assoc]
        _ ≤ q * E (rho * a ^ j) := hstep _ (hscale j)
        _ ≤ q * (D * q ^ j) := mul_le_mul_of_nonneg_left ih hq.le
        _ = D * q ^ (j + 1) := by rw [pow_succ]; ring
  have hratio : 0 < r / rho := div_pos hr.1 hrho
  have hratio1 : r / rho ≤ 1 := (div_le_one hrho).mpr hr.2
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one hratio hratio1 ha ha1
  have hrj : r ≤ rho * a ^ j := by
    simpa only [mul_comm] using (div_le_iff₀ hrho).mp hjhi
  have hupper : E r ≤ D * q ^ j := (hmono hr (hscale j) hrj).trans (hiter j)
  have hpower : q ^ (j + 1) < (r / rho) ^ beta := by
    have hh := Real.rpow_lt_rpow (pow_nonneg ha.le _) hjlo hbeta
    simpa only [← Real.rpow_pow_comm ha.le, haq] using hh
  have hqbound : q ^ j ≤ r ^ beta / (q * rho ^ beta) := by
    apply (le_div_iff₀ (mul_pos hq (Real.rpow_pos_of_pos hrho _))).mpr
    rw [Real.div_rpow hr.1.le hrho.le] at hpower
    have hh := (lt_div_iff₀ (Real.rpow_pos_of_pos hrho beta)).mp hpower
    rw [pow_succ] at hh
    exact (by simpa only [mul_assoc] using hh.le)
  exact hupper.trans ((mul_le_mul_of_nonneg_left hqbound hD).trans_eq (by ring))

theorem m64Morrey_exists_uniform_power_of_contraction
    {rho q D : ℝ} (hrho : 0 < rho) (hq : 0 < q) (hq1 : q < 1) (hD : 0 ≤ D) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ E : ℝ → ℝ, MonotoneOn E (Ioc 0 rho) → E rho ≤ D →
        (∀ r ∈ Ioc 0 rho, E (r * Real.exp (-1)) ≤ q * E r) →
        ∀ r ∈ Ioc 0 rho, E r ≤ K * r ^ beta := by
  refine ⟨-Real.log q, neg_pos.mpr (Real.log_neg hq hq1),
    D / (q * rho ^ (-Real.log q)), by positivity, ?_⟩
  intro E hmono hbase hstep r hr
  exact m64Morrey_energy_le_power_of_contraction hrho hq hq1 hD hmono hbase hstep hr

end PoincareConjecture
