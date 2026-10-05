import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.SquareShellSequenceHomeomorph
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual locally PL punctured-square compression

Dyadic source shells approach the omitted center. Their
target shells approach a prescribed positive inner square,
while the entire outer shell is fixed. The actual gluing
theorem produces a PL open partial homeomorphism, without
using a non-PL rational radial formula. See Hatcher p. 7,
Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Filter Topology Geometry

namespace SquareShell

/-- The positive dyadic source radii start at two and have
first inner radius one. See M76 derivation 270. -/
noncomputable def dyadicSourceRadius (n : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ n

/-- Target radii fix the first whole shell and tend to the
prescribed omitted positive inner radius. See M76 derivation 270. -/
noncomputable def dyadicTargetRadius (ρ : ℝ) : ℕ → ℝ
  | 0 => 2
  | n + 1 => ρ + (1 - ρ) * (1 / 2 : ℝ) ^ n

/-- Source dyadic radii strictly decrease. See
M76 derivation 270. -/
theorem strictAnti_dyadicSourceRadius : StrictAnti dyadicSourceRadius := by
  apply strictAnti_nat_of_succ_lt
  intro n
  dsimp only [dyadicSourceRadius]
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

/-- Every source radius is strictly above the omitted
center. See M76 derivation 270. -/
theorem dyadicSourceRadius_pos (n : ℕ) : 0 < dyadicSourceRadius n :=
  mul_pos (by norm_num) (pow_pos (by norm_num) n)

/-- The source radii tend to the omitted center. See
M76 derivation 270. -/
theorem tendsto_dyadicSourceRadius : Tendsto dyadicSourceRadius atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  simpa only [mul_zero] using h.const_mul 2

/-- A limiting target radius below one gives a strictly
decreasing target sequence, including its first fixed shell.
See M76 derivation 270. -/
theorem strictAnti_dyadicTargetRadius {ρ : ℝ} (hρ : ρ < 1) :
    StrictAnti (dyadicTargetRadius ρ) := by
  apply strictAnti_nat_of_succ_lt
  rintro (_ | n)
  · dsimp [dyadicTargetRadius]
    linarith
  · dsimp only [dyadicTargetRadius]
    rw [pow_succ]
    nlinarith [mul_pos (sub_pos.mpr hρ) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)]

/-- Every target radius is strictly outside its limiting
inner square. See M76 derivation 270. -/
theorem lt_dyadicTargetRadius {ρ : ℝ} (hρ : ρ < 1) (n : ℕ) :
    ρ < dyadicTargetRadius ρ n := by
  cases n with
  | zero => dsimp [dyadicTargetRadius]; linarith
  | succ n =>
    dsimp only [dyadicTargetRadius]
    have hpos := mul_pos (sub_pos.mpr hρ) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    linarith

/-- The target sequence tends to its prescribed omitted
positive inner radius. See M76 derivation 270. -/
theorem tendsto_dyadicTargetRadius (ρ : ℝ) :
    Tendsto (dyadicTargetRadius ρ) atTop (𝓝 ρ) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  simpa only [dyadicTargetRadius, mul_zero, add_zero] using
    tendsto_const_nhds.add (h.const_mul (1 - ρ))

/-- A punctured open square has an actual PL homeomorphism
onto the annulus outside any prescribed radius strictly
between zero and one. The entire shell of radii one through
two is fixed by the total representative. See Hatcher p. 7,
Hamilton p. 66 and M76 derivation 270. -/
theorem exists_punctured_square_compression {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∃ H : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      H.source = {x | ‖x‖ ∈ Ioo 0 2} ∧
      H.target = {y | ‖y‖ ∈ Ioo ρ 2} ∧
      H ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧ EqOn H id (shell 1 2) := by
  obtain ⟨H, hHS, hHT, hPL, hval⟩ := exists_sequence_openPartialHomeomorph
    (c := 0) (d := ρ) le_rfl hρ.le strictAnti_dyadicSourceRadius
    (strictAnti_dyadicTargetRadius hρone) dyadicSourceRadius_pos
    (lt_dyadicTargetRadius hρone) tendsto_dyadicSourceRadius (tendsto_dyadicTargetRadius ρ)
  refine ⟨H, ?_, ?_, hPL, ?_⟩
  · simpa only [dyadicSourceRadius, pow_zero, mul_one] using hHS
  · simpa only [dyadicTargetRadius] using hHT
  · intro x hx
    have hx' : x ∈ shell (dyadicSourceRadius 1) (dyadicSourceRadius 0) := by
      norm_num [dyadicSourceRadius] at ⊢
      exact hx
    apply (hval 0 x hx').2
    · dsimp [dyadicSourceRadius, dyadicTargetRadius]
      ring
    · norm_num [dyadicSourceRadius, dyadicTargetRadius]

end SquareShell
