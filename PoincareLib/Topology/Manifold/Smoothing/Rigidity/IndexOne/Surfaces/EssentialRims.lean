import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.SourceRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.StandardBoundaryTori

/-!
# Both source boundary circles are essential in the source surface

The first original torus coordinate retracts the whole source surface
onto either prescribed rim circle. This gives based group injections
without assuming connectedness or annulus recognition. See Waldhausen
1968, Section 1.3, pp. 59--60.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : V1) 1
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

/-- The complete circle on the chosen original boundary component,
as a map into the actual source surface. -/
noncomputable def sourceBoundaryCircle (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) :
    C(C, sourceSurface phi theta) where
  toFun c :=
    let z := (sourceRimCoordinates phi theta F).symm ⟨(b, c), hb⟩
    ⟨z.val, z.property.1⟩
  continuous_toFun := by fun_prop

/-- The pointwise boundary mark uses the original handle coordinates. -/
theorem sourceBoundaryCircle_original_point (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) (c : C) :
    (sourceBoundaryCircle phi theta F b hb c : X) =
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (hamiltonOneHierarchyCoordinates.symm ((b, c), theta)) : X) := rfl

theorem sourceBoundaryCircle_mem_frontier (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) (c : C) :
    (sourceBoundaryCircle phi theta F b hb c : X) ∈ frontier R :=
  ((sourceRimCoordinates phi theta F).symm ⟨(b, c), hb⟩).property.2

/-- The unchanged first circle coordinate on the entire source surface. -/
noncomputable def sourceSurfaceCircleProjection (phi : C(H, H)) (theta : C) :
    C(sourceSurface phi theta, C) where
  toFun z := (hamiltonOneHierarchyCoordinates
    (latticeHandleDomainEquiv (Fin 1) (Fin 2) L
      ⟨z.val, sourceSurface_subset phi theta z.property⟩)).1.2
  continuous_toFun := by fun_prop

theorem sourceBoundaryCircle_leftInverse (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) :
    Function.LeftInverse (sourceSurfaceCircleProjection phi theta)
      (sourceBoundaryCircle phi theta F b hb) := by
  intro c
  change (hamiltonOneHierarchyCoordinates (latticeHandleDomainEquiv (Fin 1) (Fin 2) L
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
      (hamiltonOneHierarchyCoordinates.symm ((b, c), theta))))).1.2 = c
  rw [Homeomorph.apply_symm_apply, hamiltonOneHierarchyCoordinates.apply_symm_apply]

/-- Every based rim group injects into the actual source surface group. -/
theorem sourceBoundaryCircle_pi1_injective (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) (c : C) :
    Function.Injective (FundamentalGroup.map (sourceBoundaryCircle phi theta F b hb) c) :=
  FundamentalGroup.map_injective_of_leftInverse _ _
    (sourceBoundaryCircle_leftInverse phi theta F b hb) c

/-- The same rim circle also injects into the original ambient handle.
This controls compression inside the handle, not only inside the surface. -/
theorem sourceBoundaryCircle_ambient_pi1_injective (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) (c : C) :
    Function.Injective (FundamentalGroup.map
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)).comp
        (sourceBoundaryCircle phi theta F b hb)) c) := by
  let r : C(X, C) := ⟨fun x => hamiltonLowerLatticePiEquiv (Fin 2) x.2 0,
    (continuous_apply 0).comp
      ((hamiltonLowerLatticePiEquiv (Fin 2)).continuous.comp continuous_snd)⟩
  apply FundamentalGroup.map_injective_of_leftInverse _ r
  exact sourceBoundaryCircle_leftInverse phi theta F b hb

/-- At either old boundary circle the whole source surface has
nontrivial based fundamental group, witnessed by the original circle. -/
theorem sourceSurface_nontrivial_pi1_at_boundary (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : V1)‖ = 1) :
    Nontrivial (FundamentalGroup (sourceSurface phi theta)
      (sourceBoundaryCircle phi theta F b hb 0)) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : Nontrivial (FundamentalGroup C 0) := AddCircle.nontrivial_fundamentalGroup_zero p
  exact (sourceBoundaryCircle_pi1_injective phi theta F b hb 0).nontrivial

end PoincareMT.M76.HamiltonIntervalTorus
