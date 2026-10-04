import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice

/-!
# Original signed link arcs from marked region incidence

The original hemisphere inclusions determine the weak sign
of each link arc. Their complete common zero set supplies
the converse, including the marked endpoints. See Alexander
1924, pp. 6--8 and M76 derivation 295.
-/

set_option autoImplicit false

open Set

namespace Set

/-- Actual rim inclusions, height-side region unions and
the original link zero set identify both complete signed
link arcs. Only the original sets and real-valued height
are used. See Alexander pp. 6--8 and derivation 295. -/
theorem four_disk_signed_link_arcs {X : Type*}
    (arc disk : Bool × Bool → Set X) {P marks : Set X} (f : X → ℝ)
    (hrim : ∀ i, arc (false, i.2) ∪ arc (true, i.1) ⊆ disk i)
    (hlink : arc (true, false) ∪ arc (true, true) = P)
    (hpos : disk (false, false) ∪ disk (false, true) ⊆ {x | 0 ≤ f x})
    (hneg : disk (true, false) ∪ disk (true, true) ⊆ {x | f x ≤ 0})
    (hzero : P ∩ {x | f x = 0} ⊆ marks)
    (hmarks : ∀ i : Bool, marks ⊆ arc (true, i)) :
    arc (true, false) = P ∩ {x | 0 ≤ f x} ∧
      arc (true, true) = P ∩ {x | f x ≤ 0} := by
  have hapos : arc (true, false) ⊆ {x | 0 ≤ f x} :=
    fun x hx => hpos (Or.inl (hrim (false, false) (Or.inr hx)))
  have haneg : arc (true, true) ⊆ {x | f x ≤ 0} :=
    fun x hx => hneg (Or.inl (hrim (true, false) (Or.inr hx)))
  constructor
  · apply Subset.antisymm
    · exact fun x hx => ⟨hlink.subset (Or.inl hx), hapos hx⟩
    · intro x hx
      rcases hlink.symm.subset hx.1 with hp | hn
      · exact hp
      · exact hmarks false (hzero ⟨hx.1, le_antisymm (haneg hn) hx.2⟩)
  · apply Subset.antisymm
    · exact fun x hx => ⟨hlink.subset (Or.inr hx), haneg hx⟩
    · intro x hx
      rcases hlink.symm.subset hx.1 with hp | hn
      · exact hmarks true (hzero ⟨hx.1, le_antisymm hx.2 (hapos hp)⟩)
      · exact hn

end Set
