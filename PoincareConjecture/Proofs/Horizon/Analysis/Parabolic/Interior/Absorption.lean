import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter
open scoped Topology

namespace Poincare.Parabolic.Interior

theorem nonpos_of_le_mul_succ_of_bounded
    {u : ℕ → ℝ} {θ M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hbounded : ∀ k, u k ≤ M) (hstep : ∀ k, u k ≤ θ * u (k + 1)) :
    ∀ k, u k ≤ 0 := by
  intro k
  have hiter : ∀ j, u k ≤ θ ^ j * u (k + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          u k ≤ θ ^ j * u (k + j) := ih
          _ ≤ θ ^ j * (θ * u (k + j + 1)) :=
            mul_le_mul_of_nonneg_left (hstep (k + j)) (pow_nonneg hθ0 j)
          _ = θ ^ (j + 1) * u (k + (j + 1)) := by
            rw [pow_succ]
            simp only [Nat.add_assoc, mul_assoc]
  have hle : ∀ j, u k ≤ θ ^ j * M := fun j =>
    (hiter j).trans (mul_le_mul_of_nonneg_left (hbounded (k + j))
      (pow_nonneg hθ0 j))
  have hlim : Tendsto (fun j : ℕ => θ ^ j * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const M
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hle)

theorem le_geometric_bound_of_le_add_mul_succ
    {u : ℕ → ℝ} {A b θ M : ℝ} (hA : 0 ≤ A) (hb : 1 ≤ b)
    (hθ : 0 ≤ θ) (hsmall : θ * b < 1)
    (hbounded : ∀ k, u k ≤ M)
    (hstep : ∀ k, u k ≤ A * b ^ k + θ * u (k + 1)) :
    ∀ k, u k ≤ A * b ^ k / (1 - θ * b) := by
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hden : 0 < 1 - θ * b := sub_pos.mpr hsmall
  have hθ1 : θ < 1 :=
    (le_mul_of_one_le_right hθ hb).trans_lt hsmall
  let D : ℝ := A / (1 - θ * b)
  have hD : 0 ≤ D := div_nonneg hA hden.le
  have hDA : D * (1 - θ * b) = A := div_mul_cancel₀ A hden.ne'
  have hresidual := nonpos_of_le_mul_succ_of_bounded
    (u := fun k => u k - D * b ^ k) hθ hθ1
    (fun k => (sub_le_self _ (mul_nonneg hD (pow_nonneg hb0 k))).trans
      (hbounded k)) (fun k => by
        have hcancel : A * b ^ k + θ * (D * b ^ (k + 1)) = D * b ^ k := by
          rw [pow_succ]
          nlinarith [congrArg (fun x : ℝ => x * b ^ k) hDA]
        linarith [hstep k])
  intro k
  have heq : D * b ^ k = A * b ^ k / (1 - θ * b) := by
    dsimp [D]
    ring
  rw [← heq]
  exact sub_nonpos.mp (hresidual k)

end Poincare.Parabolic.Interior
