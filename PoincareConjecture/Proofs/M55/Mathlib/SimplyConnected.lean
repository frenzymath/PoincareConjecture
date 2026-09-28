import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected








set_option autoImplicit false

universe u




theorem simplyConnected_of_pathConnected_of_fundamentalGroup_subsingleton
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (h : ∀ x : X, Subsingleton (FundamentalGroup X x)) :
    SimplyConnectedSpace X := by
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨inferInstance, ?_⟩
  intro x p
  let := h x
  exact Path.Homotopic.Quotient.eq.mp
    (Subsingleton.elim (α := FundamentalGroup X x) ⟦p⟧ ⟦Path.refl x⟧)
