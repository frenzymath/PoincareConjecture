import Mathlib.Data.Set.Lattice

/-!
# Exact contact from opposite height bounds

Opposite closed height bounds force any common point into
the shared height fiber. Retaining the upper set's whole
fiber and its inclusion in the lower set identifies their
entire intersection. See Alexander 1924, pp. 6--8 and M76
derivations 248g and 284.
-/

set_option autoImplicit false

namespace Set

variable {X α : Type*} [PartialOrder α]

/-- Opposite closed height bounds identify the full contact
with the upper set's exact bottom fiber, provided that fiber
lies in the lower set. Empty fibers and arbitrary partial
orders are allowed. See Alexander pp. 6--8 and derivation248g. -/
theorem inter_eq_of_height_separation (A : X → α) {c : α} {B T d : Set X}
    (hB : B ⊆ {x | A x ≤ c}) (hT : T ⊆ {x | c ≤ A x})
    (hcut : T ∩ {x | A x = c} = d) (hdB : d ⊆ B) : B ∩ T = d := by
  apply Subset.antisymm
  · intro x hx
    exact hcut.subset ⟨hx.2, le_antisymm (hB hx.1) (hT hx.2)⟩
  · intro x hx
    exact ⟨hdB hx, (hcut.symm.subset hx).1⟩

end Set
