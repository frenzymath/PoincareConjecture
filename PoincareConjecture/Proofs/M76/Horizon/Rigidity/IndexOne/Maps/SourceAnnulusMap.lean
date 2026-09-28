import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.EssentialRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.AnnulusGroups
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : Fin 1 → ℝ) 1
local notation "C" => AddCircle (4 * (128 : ℝ))

noncomputable def sourceAnnulusMap (phi : C(H, H)) (theta : C) :
    C(sourceSurface phi theta, D × C) where
  toFun x := (hamiltonOneHierarchyCoordinates
    (phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L
      ⟨x.val, sourceSurface_subset phi theta x.property⟩))).1
  continuous_toFun := by fun_prop

theorem sourceAnnulusMap_on_rim (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (x : ↥(sourceSurface phi theta ∩ frontier R)) :
    sourceAnnulusMap phi theta ⟨x.val, x.property.1⟩ =
      (sourceRimCoordinates phi theta F x : D × C) := by
  let y : R := ⟨x.val, sourceSurface_subset phi theta x.property.1⟩
  let E := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  have hy : E y ∈ B :=
    (Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L) y).mpr
      x.property.2
  have hfix : phi (E y) = E y := (F.apply_one (E y)).symm.trans (F.eq_fst 1 hy)
  change (hamiltonOneHierarchyCoordinates (phi (E y))).1 =
    (hamiltonOneHierarchyCoordinates (E y)).1
  rw [hfix]

theorem sourceAnnulusMap_boundaryCircle (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1)
    (c : C) :
    sourceAnnulusMap phi theta (sourceBoundaryCircle phi theta F b hb c) = (b, c) := by
  let z : hamiltonOneAnnulusRim := ⟨(b, c), hb⟩
  have h := sourceAnnulusMap_on_rim phi theta F ((sourceRimCoordinates phi theta F).symm z)
  exact h.trans (congrArg Subtype.val ((sourceRimCoordinates phi theta F).apply_symm_apply z))

theorem sourceAnnulusMap_pi1_injective (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (x : sourceSurface phi theta)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x)) :
    Function.Injective (FundamentalGroup.map (sourceAnnulusMap phi theta) x) := by
  let inc : C(sourceSurface phi theta, R) :=
    ContinuousMap.inclusion (sourceSurface_subset phi theta)
  let E : C(R, H) := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  let coords : C(H, (D × C) × C) := hamiltonOneHierarchyCoordinates
  let sectionMap : C(D × C, (D × C) × C) :=
    ⟨fun y => (y, theta), continuous_id.prodMk continuous_const⟩
  have hfactor : sectionMap.comp (sourceAnnulusMap phi theta) =
      coords.comp (phi.comp (E.comp inc)) := by
    apply ContinuousMap.ext
    intro y
    apply Prod.ext
    · rfl
    · exact ((mem_sourceSurface_iff phi theta (inc y)).mp y.property).symm
  have hinc : Function.Injective (FundamentalGroup.map inc x) := by
    have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X)).comp inc := rfl
    rw [heq, FundamentalGroup.map_comp] at hinj
    exact Function.Injective.of_comp hinj
  have hfull : Function.Injective
      (FundamentalGroup.map (coords.comp (phi.comp (E.comp inc))) x) := by
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonOneHierarchyCoordinates.fundamentalGroupMulEquiv _).injective.comp
      ((F.fundamentalGroup_map_bijective _).1.comp
        (((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).fundamentalGroupMulEquiv _).injective.comp hinc))
  rw [← hfactor, FundamentalGroup.map_comp] at hfull
  exact Function.Injective.of_comp hfull

theorem sourceBoundaryCircle_pi1_bijective_of_ambient_injective
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) (c : C)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X))
      (sourceBoundaryCircle phi theta F b hb c))) :
    Function.Bijective (FundamentalGroup.map (sourceBoundaryCircle phi theta F b hb) c) := by
  have hfactor : (sourceAnnulusMap phi theta).comp (sourceBoundaryCircle phi theta F b hb) =
      (⟨fun z : C => (b, z), continuous_const.prodMk continuous_id⟩ : C(C, D × C)) := by
    apply ContinuousMap.ext
    intro z
    exact sourceAnnulusMap_boundaryCircle phi theta F b hb z
  have hcomp : Function.Bijective (FundamentalGroup.map
      ((sourceAnnulusMap phi theta).comp (sourceBoundaryCircle phi theta F b hb)) c) := by
    rw [hfactor]
    exact annulus_section_pi1_bijective b c
  rw [FundamentalGroup.map_comp] at hcomp
  refine ⟨sourceBoundaryCircle_pi1_injective phi theta F b hb c, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := hcomp.2 (FundamentalGroup.map (sourceAnnulusMap phi theta)
    (sourceBoundaryCircle phi theta F b hb c) y)
  exact ⟨z, sourceAnnulusMap_pi1_injective phi theta F _ hinj hz⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
