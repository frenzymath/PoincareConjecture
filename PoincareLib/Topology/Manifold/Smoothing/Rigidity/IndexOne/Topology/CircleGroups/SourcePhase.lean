import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Maps.SourceAnnulusMap

/-!
# Cyclic fundamental groups of the actual incompressible source phases

The original map sends the literal phase to its target interval-circle
annulus. Ambient incompressibility makes this map injective on fundamental
groups. The annulus projection then embeds every based phase group into the
actual circle group, which is cyclic by its universal covering computation.
No connected component or surface classification is assumed. See Waldhausen
(1968), Section 1.3, pp. 59--60, and Theorem 6.1, p. 77.
-/

set_option autoImplicit false
open Set Metric

namespace PoincareMT.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : Fin 1 → ℝ) 1
local notation "C" => AddCircle (4 * (128 : ℝ))

/-- At every basepoint of the actual source phase, ambient incompressibility
forces its fundamental group to be cyclic. -/
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

end PoincareMT.M76.HamiltonIntervalTorus
