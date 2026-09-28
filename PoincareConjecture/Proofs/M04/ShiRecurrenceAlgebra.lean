import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PoincareConjecture.M04

def shiTimeExponent (k l : Nat) : Nat := k - l

theorem shiTimeExponent_eq_zero_of_le {k l : Nat} (h : k ≤ l) :
    shiTimeExponent k l = 0 := by
  simp [shiTimeExponent, Nat.sub_eq_zero_of_le h]

theorem shiTimeExponent_pos_of_lt {k l : Nat} (h : l < k) :
    0 < shiTimeExponent k l := by
  simp only [shiTimeExponent]
  omega

theorem shiTimeExponent_cast_eq_max_sub (k l : Nat) :
    ((shiTimeExponent k l : Nat) : Real) =
      max ((k : Real) - (l : Real)) 0 := by
  by_cases h : l ≤ k
  · have hreal : 0 ≤ (k : Real) - (l : Real) := by
      exact sub_nonneg.mpr (Nat.cast_le.mpr h)
    rw [shiTimeExponent, Nat.cast_sub h]
    exact (max_eq_left hreal).symm
  · have hkl : k ≤ l := by omega
    have hsub : k - l = 0 := Nat.sub_eq_zero_of_le hkl
    have hreal : (k : Real) - (l : Real) ≤ 0 := by
      exact sub_nonpos.mpr (Nat.cast_le.mpr hkl)
    rw [shiTimeExponent, hsub]
    simpa using (max_eq_right hreal).symm

noncomputable def shiReactionWeight : Nat → Nat
  | 0 => 12
  | m + 1 => 2 * shiReactionWeight m + 6 * m + 25

theorem shiReactionWeight_zero : shiReactionWeight 0 = 12 := by
  rfl

theorem shiReactionWeight_succ (m : Nat) :
    shiReactionWeight (m + 1) = 2 * shiReactionWeight m + 6 * m + 25 := by
  rfl

theorem shiReactionWeight_pos (m : Nat) : 0 < shiReactionWeight m := by
  induction m with
  | zero => simp [shiReactionWeight]
  | succ m ih =>
      simp only [shiReactionWeight]
      omega

theorem shiReactionWeight_ge_order (m : Nat) :
    m + 1 ≤ shiReactionWeight m := by
  induction m with
  | zero => simp [shiReactionWeight]
  | succ m ih =>
      simp only [shiReactionWeight]
      omega

end PoincareConjecture.M04
