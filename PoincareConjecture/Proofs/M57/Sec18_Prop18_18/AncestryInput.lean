import PoincareConjecture.Definitions.M57Transport
import PoincareConjecture.Proofs.M57.Sec18_Prop18_18.EventInput










set_option autoImplicit false

universe u

namespace PoincareConjecture



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

end PoincareConjecture
