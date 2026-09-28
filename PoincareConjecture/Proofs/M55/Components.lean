import PoincareConjecture.Definitions.M55ChildComponents
import PoincareConjecture.Proofs.M55.Mathlib.SimplyConnected

set_option autoImplicit false

universe u

namespace PoincareConjecture

noncomputable def RepairedSurgeryGroupEffectsData.childComponents
    {A B : GeneralizedSliceCarrier.{u}} {C : SurgeryTopologyConclusion A B}
    (E : RepairedSurgeryGroupEffectsData C)
    (parent_groups_subsingleton :
      ∀ (i : Fin C.piece_count) (hi : C.kind i = .survivor)
        (x : (C.piece i).carrier),
        Subsingleton (FundamentalGroup A.carrier (E.parent_basepoint i hi x))) :
    RepairedChildComponentsData C E := by
  have groups : ∀ (i : Fin C.piece_count), C.kind i = .survivor →
      ∀ x : (C.piece i).carrier,
        Subsingleton (FundamentalGroup (C.piece i).carrier x) := by
    intro i hi x
    let := parent_groups_subsingleton i hi x
    exact (E.piece_effect i hi x).target_subsingleton
  refine
    { survivor_group_subsingleton := groups
      survivor_simply_connected := ?_
      survivor_component_point := fun i hi => (C.survivor_component i hi).choose
      survivor_component_point_spec := fun i hi => (C.survivor_component i hi).choose_spec }
  intro i hi
  let : ConnectedSpace (C.piece i).carrier :=
    connectedSpace_iff_univ.mpr (C.piece_connected i)
  let : LocallyPathConnectedSpace (C.piece i).carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) (C.piece i).carrier
  let : PathConnectedSpace (C.piece i).carrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact simplyConnected_of_pathConnected_of_fundamentalGroup_subsingleton
    (C.piece i).carrier (groups i hi)

end PoincareConjecture
