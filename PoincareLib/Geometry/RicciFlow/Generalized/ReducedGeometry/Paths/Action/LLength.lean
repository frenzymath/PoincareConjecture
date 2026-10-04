import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Generalized L-action and its infimum

Morgan-Tian Definition 6.2, p. 106, and Definitions 6.25-6.27, pp. 116-117.
A supplied minimizing path realizes the action infimum. No existence of a
minimizer is inferred from finiteness of the infimum.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

/-- A path contributes its own action to the set in Definition 6.2, p. 106. -/
theorem action_mem_actionSet (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14BackwardLAction G p ∈ M14ActionSet G T τ₁ τ₂ x y :=
  ⟨p, rfl⟩

/-- Minimality gives a least action, as in Definitions 6.25-6.27, pp. 116-117. -/
theorem isLeast_action_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) :
    IsLeast (M14ActionSet G T τ₁ τ₂ x y) (M14BackwardLAction G p) := by
  refine ⟨action_mem_actionSet p, ?_⟩
  rintro a ⟨q, rfl⟩
  exact hp q

/-- A minimizing path supplies both finite-value hypotheses, Definition 6.27, p. 117. -/
theorem finiteValueDomain_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) : M14FiniteValueDomain G T τ₁ τ₂ x y := by
  have hleast := isLeast_action_of_minimizing p hp
  exact ⟨⟨_, hleast.1⟩, ⟨_, hleast.2⟩⟩

/-- An attained action domain is finite, with no converse asserted, p. 117. -/
theorem finiteValueDomain_of_attained
    (h : M14AttainedDomain G T τ₁ τ₂ x y) :
    M14FiniteValueDomain G T τ₁ τ₂ x y := by
  obtain ⟨p, hp⟩ := h
  exact finiteValueDomain_of_minimizing p hp

/-- A minimizing path realizes the defining infimum, Definition 6.27, p. 117. -/
theorem action_eq_actionValue_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) :
    M14BackwardLAction G p = M14ActionValue G T τ₁ τ₂ x y :=
  (isLeast_action_of_minimizing p hp).csInf_eq.symm

/-- On the finite-value domain, the infimum bounds each competitor, p. 117. -/
theorem actionValue_le_action (h : M14FiniteValueDomain G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14ActionValue G T τ₁ τ₂ x y ≤ M14BackwardLAction G p :=
  csInf_le h.2 (action_mem_actionSet p)

/-- Equality with a finite action infimum characterizes minimality, p. 117. -/
theorem isMinimizing_iff_action_eq_actionValue
    (h : M14FiniteValueDomain G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14IsMinimizing p ↔
      M14BackwardLAction G p = M14ActionValue G T τ₁ τ₂ x y := by
  refine ⟨action_eq_actionValue_of_minimizing p, ?_⟩
  intro hp q
  rw [hp]
  exact actionValue_le_action h q

/-- Reduced length on a minimizing path uses the absolute final time,
Morgan-Tian Definition 6.45, p. 129. -/
theorem reducedLengthValue_eq_of_minimizing (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hp : M14IsMinimizing p) :
    M14ReducedLengthValue G T τ₁ τ₂ x y =
      M14BackwardLAction G p / (2 * Real.sqrt τ₂) := by
  rw [M14ReducedLengthValue, ← action_eq_actionValue_of_minimizing p hp]

end PoincareMT.M14
