import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring









set_option autoImplicit false

namespace Poincare.Parabolic.Interior

theorem exists_uniform_absorption_scale
    (C d H L C1 C2 Ct : ℝ) (hC : 0 < C)
    (hd : 0 ≤ d) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCt : 0 ≤ Ct) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ∃ A : ℝ, 0 < A ∧
      ∀ r B M : ℝ, 0 < r → r ≤ 1 → 0 ≤ B → 0 ≤ M →
        C * ((d * H * M +
          d * L * (2 * (C1 / r) * (2 * B / r + M * r) + (C2 / r ^ 2) * B) /
            (r / 2) ^ (1 / 2 : ℝ)) * (q * r ^ 2) ^ (1 / 4 : ℝ) +
          2 * Ct * B / (q * r ^ 2)) ≤ A * B / r ^ 2 + (1 / 8 : ℝ) * M := by
  let D := C * (d * H + 2 * d * L * C1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let k := 1 / (8 * (D + 1))
  have hk : 0 < k := by dsimp [k]; positivity
  have hk1 : k ≤ 1 := by
    dsimp [k]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hkD : k * D ≤ (1 / 8 : ℝ) := by
    dsimp [k]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : 0 < 8 * (D + 1))).mpr
    linarith
  let q := k ^ 4 / 4
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    have hp : k ^ 4 ≤ 1 := pow_le_one₀ hk.le hk1
    dsimp [q]
    linarith
  let A := C * k * d * L * (4 * C1 + C2) + 2 * C * Ct / q + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨q, hq, hq1, A, hA, ?_⟩
  intro r B M hr hr1 hB hM
  let z := Real.sqrt (r / 2)
  have hz : 0 < z := Real.sqrt_pos.mpr (by positivity)
  have hzsq : z ^ 2 = r / 2 := Real.sq_sqrt (by positivity)
  have hz1 : z ≤ 1 := by nlinarith
  have hz4 : z ^ 4 = r ^ 2 / 4 := by
    calc
      z ^ 4 = (z ^ 2) ^ 2 := by ring
      _ = (r / 2) ^ 2 := by rw [hzsq]
      _ = r ^ 2 / 4 := by ring
  have hquarter : (q * r ^ 2) ^ (1 / 4 : ℝ) = k * z := by
    have heq : q * r ^ 2 = (k * z) ^ 4 := by
      dsimp [q]
      rw [mul_pow, hz4]
      ring
    rw [heq, ← Real.rpow_natCast_mul (mul_nonneg hk.le hz.le)]
    norm_num
  have hhalf : (r / 2) ^ (1 / 2 : ℝ) = z := (Real.sqrt_eq_rpow _).symm
  rw [hquarter, hhalf]
  have hcoef : C * k * (d * H * z + 2 * d * L * C1) ≤ (1 / 8 : ℝ) := by
    calc
      C * k * (d * H * z + 2 * d * L * C1) ≤
          C * k * (d * H + 2 * d * L * C1) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hk.le)
        exact add_le_add (mul_le_of_le_one_right (mul_nonneg hd hH) hz1) le_rfl
      _ = k * D := by dsimp [D]; ring
      _ ≤ (1 / 8 : ℝ) := hkD
  have heq : C * ((d * H * M +
      d * L * (2 * (C1 / r) * (2 * B / r + M * r) + (C2 / r ^ 2) * B) / z) *
      (k * z) + 2 * Ct * B / (q * r ^ 2)) =
      C * k * (d * H * z + 2 * d * L * C1) * M + (A - 1) * B / r ^ 2 := by
    dsimp [A]
    field_simp
    ring
  rw [heq]
  have hterm := mul_le_mul_of_nonneg_right hcoef hM
  have hforcing : (A - 1) * B / r ^ 2 ≤ A * B / r ^ 2 := by gcongr; linarith
  linarith

end Poincare.Parabolic.Interior
