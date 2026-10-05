import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Event.EventInput

/-!
# Comparison inputs along the literal selected ancestry path

For the class transport before Morgan--Tian Proposition 18.18 (pp. 430-431),
assemble every event input on the path from Definition 18.2 (pp. 419-420).
All component and basepoint identifications are literal, and the target
point path uses the exact supplied comparison provider's output.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The Poincare ancestry supplies all actual local comparison inputs and
basepoint paths needed for the class transport on pp. 430-431. -/
theorem m57PoincareAncestryInput
    (P02 : RepairedClosedTopologyProvider.{u}) (G53 : RepairedSphereSeparationTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow) (P : M56PoincareAncestryData D.flow L)
    (K : RepairedComparisonMapData D) (C : RepairedComparisonHomotopyData D K)
    (T : ℝ) (hT : T ∈ D.flow.time_domain) (x : (D.flow.slice T).carrier) :
    Nonempty (RepairedAncestryTransportInput D P.witness
      (P.ancestry.path_for T hT x) K C) := by
  let A := P.ancestry.path_for T hT x
  let input (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier) :=
    @m57EventInput P02 G53 g₀ D L P T A S hS hpost
  refine ⟨{
    event_input := input
    event_parent_path := fun _ _ _ => HEq.rfl
    event_child_path := fun _ _ _ => HEq.rfl
    event_topology_path := fun S hS hpost => (P.topology_source S.1 hS hpost).symm
    event_survivor_region_path := fun S hS hpost => (A.event_survivor S hS hpost).1.symm
    event_child_range := fun _ _ _ => rfl
    event_parent_basepoint_path := fun _ _ _ => HEq.rfl
    event_child_basepoint_path := fun _ _ _ => HEq.rfl
    event_target_basepoint_bridge := ?_
    regular_basepoint_bridge := ?_ }⟩
  · intro S hS hpost
    let := hpost
    intro hdelta hh
    let O := Classical.choice (C.transport S.1 hS (input S hS hpost) hdelta hh)
    exact ⟨O.val.comparison.target_basepoint, HEq.rfl,
      m57ComponentPointPath (A.component S) _ _⟩
  · intro a b hab hdisjoint
    exact m57ComponentPointPath (A.component b) _ _

end PoincareMT
