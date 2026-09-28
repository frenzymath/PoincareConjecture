import PoincareConjecture.Proofs.M76.Mathlib.FiniteCycleLabels

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V : Type*}

theorem ConnectedComponent.ncard_neighborSet (G : SimpleGraph V)
    (C : G.ConnectedComponent) (v : C) :
    (C.toSimpleGraph.neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  have he : Subtype.val '' C.toSimpleGraph.neighborSet v = G.neighborSet v.val := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hw
      exact ⟨⟨w, C.mem_supp_of_adj_mem_supp v.property hw⟩, hw, rfl⟩
  rw [← he, ncard_image_of_injective _ Subtype.val_injective]

theorem exists_cyclic_component_labels_of_two_neighbors [Finite V]
    (G : SimpleGraph V) (hdegree : ∀ v, (G.neighborSet v).ncard = 2)
    (C : G.ConnectedComponent) :
    ∃ (n : ℕ) (e : Fin (n + 3) ≃ C), ∀ x y : C,
      G.Adj x.val y.val ↔ ∃ i, (e i = x ∧ e (i + 1) = y) ∨
        (e i = y ∧ e (i + 1) = x) := by
  apply C.toSimpleGraph.exists_cyclic_labels_of_two_neighbors C.connected_toSimpleGraph
  intro v
  rw [C.ncard_neighborSet, hdegree]

end SimpleGraph
