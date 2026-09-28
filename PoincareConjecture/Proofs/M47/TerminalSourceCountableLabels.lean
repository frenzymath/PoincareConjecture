import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Filter.AtTopBot.Basic









set_option autoImplicit false

namespace PoincareConjecture.M47

private def countableLabelOfPair (N : ℕ → ℕ) (z : ℕ × ℕ) : Σ j, Fin (N j + 1) :=
  ⟨z.1, ⟨z.2 % (N z.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩⟩


def terminalSourceCountableLabel (N : ℕ → ℕ) (n : ℕ) : Σ j, Fin (N j + 1) :=
  countableLabelOfPair N (Nat.unpair n)


theorem terminalSourceCountableLabel_zero (N : ℕ → ℕ) :
    terminalSourceCountableLabel N 0 = ⟨0, 0⟩ := by
  rw [terminalSourceCountableLabel, Nat.unpair_zero]
  apply congrArg (fun q : Fin (N 0 + 1) => (⟨0, q⟩ : Σ j, Fin (N j + 1)))
  apply Fin.ext
  exact Nat.zero_mod _


theorem terminalSourceCountableLabel_pair (N : ℕ → ℕ) (j : ℕ) (i : Fin (N j + 1)) :
    terminalSourceCountableLabel N (Nat.pair j i.val) = ⟨j, i⟩ := by
  rw [terminalSourceCountableLabel, Nat.unpair_pair]
  apply congrArg (fun q : Fin (N j + 1) => (⟨j, q⟩ : Σ j, Fin (N j + 1)))
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt


theorem terminalSourceCountableLabel_surjective (N : ℕ → ℕ) :
    Function.Surjective (terminalSourceCountableLabel N) := by
  rintro ⟨j, i⟩
  exact ⟨Nat.pair j i.val, terminalSourceCountableLabel_pair N j i⟩


theorem terminalSourceCountableLabel_eventually_le (N : ℕ → ℕ) (n : ℕ) :
    ∀ᶠ k in Filter.atTop, (terminalSourceCountableLabel N n).1 ≤ k :=
  Filter.eventually_ge_atTop _

end PoincareConjecture.M47
