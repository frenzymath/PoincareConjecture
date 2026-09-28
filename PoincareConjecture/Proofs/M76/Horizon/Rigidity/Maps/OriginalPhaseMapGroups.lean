import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

noncomputable def hamiltonZeroPhaseMap (phi : C(H0, H0)) (theta : C0) :
    C((hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0), C0 × C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).1,
    continuous_fst.comp (hamiltonZeroHierarchyCoordinates.continuous.comp
      (phi.continuous.comp (hamiltonZeroAmbientEquiv.continuous.comp continuous_subtype_val)))⟩

theorem hamiltonZeroPhaseMap_pi1_injective (phi : C(H0, H0))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) (theta : C0)
    (x : hamiltonZeroCircleMap phi ⁻¹' {theta})
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C((hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0), X0)) x)) :
    Function.Injective (FundamentalGroup.map (hamiltonZeroPhaseMap phi theta) x) := by
  let M := hamiltonZeroCircleMap phi ⁻¹' {theta}
  let inc : C(M, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let coords : C(H0, (C0 × C0) × C0) := hamiltonZeroHierarchyCoordinates
  let sectionMap : C(C0 × C0, (C0 × C0) × C0) :=
    ⟨fun y => (y, theta), continuous_id.prodMk continuous_const⟩
  have hfactor : sectionMap.comp (hamiltonZeroPhaseMap phi theta) =
      coords.comp (phi.comp (ambient.comp inc)) := by
    apply ContinuousMap.ext
    intro y
    apply Prod.ext
    · rfl
    · exact y.property.symm
  have hi : Function.Injective
      (FundamentalGroup.map (coords.comp (phi.comp (ambient.comp inc))) x) := by
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroHierarchyCoordinates.fundamentalGroupMulEquiv
      (phi (ambient (inc x)))).injective.comp
      ((F.fundamentalGroup_map_bijective (ambient (inc x))).1.comp
        ((hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv (inc x)).injective.comp hinj))
  rw [← hfactor, FundamentalGroup.map_comp] at hi
  exact Function.Injective.of_comp hi

end PoincareConjecture.M76
