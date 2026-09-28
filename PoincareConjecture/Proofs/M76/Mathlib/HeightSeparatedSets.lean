import Mathlib.Data.Set.Lattice











set_option autoImplicit false

namespace Set

variable {X α : Type*} [PartialOrder α]





theorem inter_eq_of_height_separation (A : X → α) {c : α} {B T d : Set X}
    (hB : B ⊆ {x | A x ≤ c}) (hT : T ⊆ {x | c ≤ A x})
    (hcut : T ∩ {x | A x = c} = d) (hdB : d ⊆ B) : B ∩ T = d := by
  apply Subset.antisymm
  · intro x hx
    exact hcut.subset ⟨hx.2, le_antisymm (hB hx.1) (hT hx.2)⟩
  · intro x hx
    exact ⟨hdB hx, (hcut.symm.subset hx).1⟩

end Set
