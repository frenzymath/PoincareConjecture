import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourceAnnulusMap

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : Fin 1 → ℝ) 1
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem sourceSurface_pi1_isCyclic_of_ambient_injective
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (x : sourceSurface phi theta)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x)) :
    IsCyclic (FundamentalGroup (sourceSurface phi theta) x) := by
  let q : C(D × C, C) := ⟨Prod.snd, continuous_snd⟩
  let y := sourceAnnulusMap phi theta x
  let : IsCyclic (FundamentalGroup C y.2) :=
    circleFundamentalGroup_isCyclic (4 * (128 : ℝ)) (by norm_num) y.2
  exact isCyclic_of_injective
    ((FundamentalGroup.map q y).comp (FundamentalGroup.map (sourceAnnulusMap phi theta) x))
    ((annulus_projection_pi1_bijective y).1.comp
      (sourceAnnulusMap_pi1_injective phi theta F x hinj))

end PoincareConjecture.M76.HamiltonIntervalTorus
