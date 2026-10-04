import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card

/-! # The two nonalternating pairings of four square contacts -/

set_option autoImplicit false

namespace Poincare.Topology

set_option synthInstance.maxSize 256 in
/-- A balanced assignment of the four corners to two components, with opposite
corners in different components, pairs corners along one coordinate direction. -/
theorem four_contacts_pairing
    (c : Fin 2 × Fin 2 → Fin 2)
    (hcard : ∀ j, (Finset.univ.filter (fun i => c i = j)).card = 2)
    (hopposite : c (0, 0) ≠ c (1, 1)) :
    (∀ i j, c i = c j ↔ i.1 = j.1) ∨
      (∀ i j, c i = c j ↔ i.2 = j.2) := by
  have h : ∀ c : Fin 2 × Fin 2 → Fin 2,
      (∀ j, (Finset.univ.filter (fun i => c i = j)).card = 2) →
      c (0, 0) ≠ c (1, 1) →
      (∀ i j, c i = c j ↔ i.1 = j.1) ∨
        (∀ i j, c i = c j ↔ i.2 = j.2) := by decide
  exact h c hcard hopposite

/-- In a balanced diagonal pairing, the other two corners form the other
component. -/
theorem four_contacts_opposite_pairing
    (c : Fin 2 × Fin 2 → Fin 2)
    (hcard : ∀ j, (Finset.univ.filter (fun i => c i = j)).card = 2)
    (hopposite : c (0, 0) = c (1, 1)) :
    c (0, 1) = c (1, 0) ∧ c (0, 0) ≠ c (0, 1) := by
  have h : ∀ c : Fin 2 × Fin 2 → Fin 2,
      (∀ j, (Finset.univ.filter (fun i => c i = j)).card = 2) →
      c (0, 0) = c (1, 1) →
      c (0, 1) = c (1, 0) ∧ c (0, 0) ≠ c (0, 1) := by decide
  exact h c hcard hopposite

end Poincare.Topology
