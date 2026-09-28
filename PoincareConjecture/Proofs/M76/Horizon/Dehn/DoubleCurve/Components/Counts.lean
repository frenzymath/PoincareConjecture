import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

def doubleLocusOn {E X : Type*} (f : E → X) (S : Set E) : Set E :=
  {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y}

noncomputable def doubleBoundaryComponentCount {E X : Type*} [TopologicalSpace E]
    (f : E → X) (S Q : Set E) : ℕ :=
  (ConnectedComponents.mk '' ((Subtype.val : doubleLocusOn f S → E) ⁻¹' Q)).ncard

noncomputable def doubleInteriorComponentCount {E X : Type*} [TopologicalSpace E]
    (f : E → X) (S Q : Set E) : ℕ :=
  (ConnectedComponents.mk '' ((Subtype.val : doubleLocusOn f S → E) ⁻¹' Q))ᶜ.ncard

end PoincareConjecture.M76.Dehn
