import PoincareLib.Topology.Manifold.Smoothing.Dehn.Topology.Mathlib.FiniteClosedComponentPartition

/-!
# Intrinsic counts of the actual disk double components

The source double locus is defined by distinct points with equal target
values. Counts refer to its connected-component quotient and literal
boundary, independently of a graph, triangulation or surgery history.
For an ordinary finite double locus these count its proper source arcs
and its source circles. See Dehn022, sections 10--11.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Dehn

/-- The actual distinct-point double locus on a specified source. -/
def doubleLocusOn {E X : Type*} (f : E → X) (S : Set E) : Set E :=
  {x | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y}

/-- Number of actual double components meeting the source boundary. -/
noncomputable def doubleBoundaryComponentCount {E X : Type*} [TopologicalSpace E]
    (f : E → X) (S Q : Set E) : ℕ :=
  (ConnectedComponents.mk '' ((Subtype.val : doubleLocusOn f S → E) ⁻¹' Q)).ncard

/-- Number of actual double components avoiding the source boundary. -/
noncomputable def doubleInteriorComponentCount {E X : Type*} [TopologicalSpace E]
    (f : E → X) (S Q : Set E) : ℕ :=
  (ConnectedComponents.mk '' ((Subtype.val : doubleLocusOn f S → E) ⁻¹' Q))ᶜ.ncard

end PoincareMT.M76.Dehn
