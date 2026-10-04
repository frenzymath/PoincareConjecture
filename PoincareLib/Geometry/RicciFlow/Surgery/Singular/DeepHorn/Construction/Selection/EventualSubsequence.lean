import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Eventual assertions from arbitrary further subsequences

The continuation argument after Morgan--Tian Claim 11.35, printed p. 291,
passes repeatedly to subsequences. This logical criterion instead recovers
an eventual assertion on the original sequence when every subsequence has
a further subsequence satisfying it. The predicate is arbitrary.

The bounded derivation is `claim11_32-sequence-reindex.md`; the proof uses
Mathlib's `Filter.extraction_of_frequently_atTop` directly.
-/

set_option autoImplicit false

open Filter

namespace PoincareMT.M32

/-- An arbitrary predicate is eventually true if every strictly increasing
subsequence has a further subsequence where it is eventually true. This is
the logical step used after Claim 11.35, printed p. 291. -/
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

end PoincareMT.M32
