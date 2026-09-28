import PoincareConjecture.Proofs.M76.Mathlib.CubeShellSequence
import Mathlib.Analysis.SpecificLimits.Basic











set_option autoImplicit false

open Set Filter Topology Geometry

namespace CubeShell






theorem exists_supported_punctured_cube_compression {r R B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRB : R < B) :
    ∃ H : OpenPartialHomeomorph Ambient Ambient,
      H.source = {x | ‖x‖ ∈ Ioo 0 B} ∧
      H.target = {y | ‖y‖ ∈ Ioo r B} ∧
      H ∈ piecewiseAffineGroupoid Ambient ∧ EqOn H id (shell R B) := by
  let a : ℕ → ℝ
    | 0 => B
    | n + 1 => R * (1 / 2 : ℝ) ^ n
  let b : ℕ → ℝ
    | 0 => B
    | n + 1 => r + (R - r) * (1 / 2 : ℝ) ^ n
  have hR : 0 < R := hr.trans hrR
  have hB : 0 < B := hR.trans hRB
  have hpow (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have ha : StrictAnti a := by
    apply strictAnti_nat_of_succ_lt
    rintro (_ | n)
    · simpa only [a, pow_zero, mul_one] using hRB
    · dsimp only [a]
      rw [pow_succ]
      nlinarith [mul_pos hR (hpow n)]
  have hb : StrictAnti b := by
    apply strictAnti_nat_of_succ_lt
    rintro (_ | n)
    · dsimp [b]
      linarith
    · dsimp only [b]
      rw [pow_succ]
      nlinarith [mul_pos (sub_pos.mpr hrR) (hpow n)]
  have habove (n : ℕ) : 0 < a n := by
    cases n with
    | zero => exact hB
    | succ n => exact mul_pos hR (hpow n)
  have hbabove (n : ℕ) : r < b n := by
    cases n with
    | zero => exact hrR.trans hRB
    | succ n =>
      dsimp only [b]
      linarith [mul_pos (sub_pos.mpr hrR) (hpow n)]
  have hpowlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have halim : Tendsto a atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [a, mul_zero] using hpowlim.const_mul R
  have hblim : Tendsto b atTop (𝓝 r) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [b, mul_zero, add_zero] using
      tendsto_const_nhds.add (hpowlim.const_mul (R - r))
  obtain ⟨H, hHS, hHT, hPL, hval⟩ := exists_sequence_openPartialHomeomorph
    (c := 0) (d := r) le_rfl hr.le ha hb habove hbabove halim hblim
  refine ⟨H, hHS, hHT, hPL, ?_⟩
  intro x hx
  have hx' : x ∈ shell (a 1) (a 0) := by
    simpa only [a, pow_zero, mul_one] using hx
  apply (hval 0 x hx').2
  · dsimp [a, b]
    ring
  · rfl

end CubeShell
