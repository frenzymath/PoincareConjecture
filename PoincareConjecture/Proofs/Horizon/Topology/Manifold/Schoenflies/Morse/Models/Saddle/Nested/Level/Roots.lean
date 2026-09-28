import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Shear
import Mathlib.Analysis.SpecialFunctions.Sqrt



noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

def lowerRoot : Real := (2 - Real.sqrt 19) / 10

def upperRoot : Real := (2 + Real.sqrt 19) / 10

def levelAbscissa (z : Real) : Real := (10 / 3) * z * (z - 1)

def levelRadicand (z : Real) : Real := 1 - z^2 - (levelAbscissa z)^2

theorem sqrt_nineteen_bounds : 4 < Real.sqrt 19 ∧ Real.sqrt 19 < 5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 19)
  have hn := Real.sqrt_nonneg (19 : Real)
  constructor <;> nlinarith

theorem lowerRoot_bounds : -(3 / 5 : Real) < lowerRoot ∧ lowerRoot < 0 := by
  have hs := sqrt_nineteen_bounds
  dsimp [lowerRoot]
  constructor <;> linarith

theorem upperRoot_bounds : (3 / 5 : Real) < upperRoot ∧ upperRoot < 1 := by
  have hs : (4 : Real) < Real.sqrt 19 := sqrt_nineteen_bounds.1
  have hs' := sqrt_nineteen_bounds.2
  dsimp [upperRoot]
  constructor <;> linarith

theorem levelRadicand_factor (z : Real) :
    levelRadicand z = (100 / 9) *
      ((z - lowerRoot) * (z - 3 / 5) * (z - upperRoot) * (1 - z)) := by
  have hroots : (z - lowerRoot) * (z - upperRoot) = z^2 - (2 / 5) * z - 3 / 20 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 19)
    dsimp [lowerRoot, upperRoot]
    nlinarith
  calc
    levelRadicand z = (100 / 9) *
        ((z^2 - (2 / 5) * z - 3 / 20) * (z - 3 / 5) * (1 - z)) := by
      dsimp [levelRadicand, levelAbscissa]
      ring
    _ = _ := by rw [← hroots]; ring

@[simp] theorem levelRadicand_lowerRoot : levelRadicand lowerRoot = 0 := by
  rw [levelRadicand_factor]
  simp

@[simp] theorem levelRadicand_three_fifths : levelRadicand (3 / 5) = 0 := by
  rw [levelRadicand_factor]
  norm_num

@[simp] theorem levelRadicand_upperRoot : levelRadicand upperRoot = 0 := by
  rw [levelRadicand_factor]
  simp

@[simp] theorem levelRadicand_one : levelRadicand 1 = 0 := by
  rw [levelRadicand_factor]
  simp

theorem levelRadicand_eq_zero_iff (z : Real) :
    levelRadicand z = 0 ↔ z = lowerRoot ∨ z = 3 / 5 ∨ z = upperRoot ∨ z = 1 := by
  constructor
  · intro hz
    rw [levelRadicand_factor] at hz
    have hp := (mul_eq_zero.mp hz).resolve_left (by norm_num : (100 / 9 : Real) ≠ 0)
    rcases mul_eq_zero.mp hp with hp | hp
    · rcases mul_eq_zero.mp hp with hp | hp
      · rcases mul_eq_zero.mp hp with hp | hp
        · exact Or.inl (sub_eq_zero.mp hp)
        · exact Or.inr (Or.inl (sub_eq_zero.mp hp))
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hp)))
    · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp hp).symm))
  · rintro (rfl | rfl | rfl | rfl) <;> simp


theorem levelRadicand_nonneg_iff (z : Real) :
    0 ≤ levelRadicand z ↔ z ∈ Icc lowerRoot (3 / 5) ∨ z ∈ Icc upperRoot 1 := by
  have hab : lowerRoot < (3 / 5 : Real) := lowerRoot_bounds.2.trans (by norm_num)
  have hbc := upperRoot_bounds.1
  have hcd := upperRoot_bounds.2
  rw [levelRadicand_factor, mul_nonneg_iff_of_pos_left (by norm_num : (0 : Real) < 100 / 9)]
  constructor
  · intro hp
    have haz : lowerRoot ≤ z := by
      by_contra hz
      have hz' : z < lowerRoot := lt_of_not_ge hz
      have hneg : (z - lowerRoot) * (z - 3 / 5) * (z - upperRoot) * (1 - z) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
          (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)) (by linarith)
      exact (not_lt_of_ge hp) hneg
    by_cases hzb : z ≤ 3 / 5
    · exact Or.inl ⟨haz, hzb⟩
    have hbz : (3 / 5 : Real) < z := lt_of_not_ge hzb
    have hcz : upperRoot ≤ z := by
      by_contra hz
      have hz' : z < upperRoot := lt_of_not_ge hz
      have hneg : (z - lowerRoot) * (z - 3 / 5) * (z - upperRoot) * (1 - z) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
          (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
      exact (not_lt_of_ge hp) hneg
    have hz1 : z ≤ 1 := by
      by_contra hz
      have hz' : 1 < z := lt_of_not_ge hz
      have hneg : (z - lowerRoot) * (z - 3 / 5) * (z - upperRoot) * (1 - z) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos (mul_pos (by linarith) (by linarith))
          (by linarith)) (by linarith)
      exact (not_lt_of_ge hp) hneg
    exact Or.inr ⟨hcz, hz1⟩
  · rintro (hz | hz)
    · exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by linarith [hz.1]) (by linarith [hz.2]))
        (by linarith [hz.2])) (by linarith [hz.2])
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith [hz.1])
        (by linarith [hz.1])) (by linarith [hz.1])) (by linarith [hz.2])

end Poincare.Manifold.Schoenflies.Saddle.Nested
