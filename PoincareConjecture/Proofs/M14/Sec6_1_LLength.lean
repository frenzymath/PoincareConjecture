import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import Mathlib.Order.ConditionallyCompleteLattice.Basic









set_option autoImplicit false

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}


theorem action_mem_actionSet (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14BackwardLAction G p ∈ M14ActionSet G T τ₁ τ₂ x y :=
  ⟨p, rfl⟩


theorem isLeast_action_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) :
    IsLeast (M14ActionSet G T τ₁ τ₂ x y) (M14BackwardLAction G p) := by
  refine ⟨action_mem_actionSet p, ?_⟩
  rintro a ⟨q, rfl⟩
  exact hp q


theorem finiteValueDomain_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) : M14FiniteValueDomain G T τ₁ τ₂ x y := by
  have hleast := isLeast_action_of_minimizing p hp
  exact ⟨⟨_, hleast.1⟩, ⟨_, hleast.2⟩⟩


theorem finiteValueDomain_of_attained
    (h : M14AttainedDomain G T τ₁ τ₂ x y) :
    M14FiniteValueDomain G T τ₁ τ₂ x y := by
  obtain ⟨p, hp⟩ := h
  exact finiteValueDomain_of_minimizing p hp


theorem action_eq_actionValue_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) :
    M14BackwardLAction G p = M14ActionValue G T τ₁ τ₂ x y :=
  (isLeast_action_of_minimizing p hp).csInf_eq.symm


theorem actionValue_le_action (h : M14FiniteValueDomain G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14ActionValue G T τ₁ τ₂ x y ≤ M14BackwardLAction G p :=
  csInf_le h.2 (action_mem_actionSet p)


theorem isMinimizing_iff_action_eq_actionValue
    (h : M14FiniteValueDomain G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14IsMinimizing p ↔
      M14BackwardLAction G p = M14ActionValue G T τ₁ τ₂ x y := by
  refine ⟨action_eq_actionValue_of_minimizing p, ?_⟩
  intro hp q
  rw [hp]
  exact actionValue_le_action h q



theorem reducedLengthValue_eq_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) :
    M14ReducedLengthValue G T τ₁ τ₂ x y =
      M14BackwardLAction G p / (2 * Real.sqrt τ₂) := by
  rw [M14ReducedLengthValue, ← action_eq_actionValue_of_minimizing p hp]

end PoincareConjecture.M14
