import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.GroupEffects
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# M55 repaired surviving-child component data

The Poincare-specific output assigns simple connectedness to every survivor
piece of an actual local surgery topology conclusion.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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

end PoincareMT
