import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simple connectedness from trivial fundamental groups

The topological bridge used for the surviving pieces in Morgan--Tian,
Proposition 15.3 (printed pp. 357-358), stated for arbitrary topological spaces.
-/

set_option autoImplicit false

universe u

/-- A path-connected space with trivial fundamental group at every basepoint
is simply connected. This is the bridge used after the survivor injections
of Morgan--Tian Proposition 15.3 (printed pp. 357-358). -/
theorem simplyConnected_of_pathConnected_of_fundamentalGroup_subsingleton
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (h : ∀ x : X, Subsingleton (FundamentalGroup X x)) :
    SimplyConnectedSpace X := by
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨inferInstance, ?_⟩
  intro x p
  let := h x
  exact Path.Homotopic.Quotient.eq.mp
    (Subsingleton.elim (α := FundamentalGroup X x) ⟦p⟧ ⟦Path.refl x⟧)
