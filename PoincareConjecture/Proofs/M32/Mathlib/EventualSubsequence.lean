import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false

open Filter

namespace PoincareConjecture.M32

theorem eventually_atTop_of_forall_subseq {P : ℕ → Prop}
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᶠ k : ℕ in atTop, P (phi (psi k))) :
    ∀ᶠ k : ℕ in atTop, P k := by
  classical
  apply Classical.byContradiction
  intro hnot
  obtain ⟨phi, hphi, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hnot)
  obtain ⟨psi, _, hgood⟩ := h phi hphi
  obtain ⟨k, hk⟩ := hgood.exists
  exact hbad (psi k) hk

end PoincareConjecture.M32
