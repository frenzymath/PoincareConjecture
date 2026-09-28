import PoincareConjecture.Definitions.M54GroupEffects
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedChildComponentsData
    {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B)
    (E : RepairedSurgeryGroupEffectsData C) where
  survivor_group_subsingleton : ∀ (i : Fin C.piece_count),
    C.kind i = .survivor →
      ∀ x : (C.piece i).carrier,
        Subsingleton (FundamentalGroup (C.piece i).carrier x)
  survivor_simply_connected : ∀ (i : Fin C.piece_count),
    C.kind i = .survivor → SimplyConnectedSpace (C.piece i).carrier
  survivor_component_point : ∀ (i : Fin C.piece_count),
    C.kind i = .survivor → B.carrier
  survivor_component_point_spec : ∀ (i : Fin C.piece_count),
    ∀ hi : C.kind i = .survivor,
      C.survivor_region i =
        connectedComponent (survivor_component_point i hi)

end PoincareConjecture
