import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCapHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCohomologyEvaluation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralHomologyZero
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleComplexConnecting

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open scoped BigOperators

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralChainZeroAugmentation (X : Type u) [TopologicalSpace X] :
    (integralChains X).X 0 ⟶ integralCoefficient :=
  ((integralChains X).iCyclesIso 0 0 (by simp) (by simp)).inv ≫
    (integralChains X).homologyπ 0 ≫ integralHomologyZeroAugmentation X

theorem integralChainZeroAugmentation_generator
    (s : C(integralSimplex 0, X)) (a : ULift.{u} Int) :
    integralChainZeroAugmentation X (integralSingularGenerator s a) = a := by
  let C := integralChains X
  let e := C.iCyclesIso 0 0 (by simp) (by simp)
  have hs : s = ContinuousMap.const (integralSimplex 0) (s default) := by
    ext t
    exact congrArg s (Subsingleton.elim t default)
  have hl : integralSingularGenerator s ≫ e.inv =
      C.liftCycles (integralSingularGenerator s) 0 (by simp) (by simp) := by
    apply (cancel_mono (C.iCycles 0)).mp
    rw [Category.assoc, iCyclesIso_inv_hom_id, Category.comp_id, liftCycles_i]
  have he : integralSingularGenerator s ≫ integralChainZeroAugmentation X = 𝟙 _ := by
    change integralSingularGenerator s ≫ e.inv ≫ C.homologyπ 0 ≫ _ = _
    rw [← Category.assoc (integralSingularGenerator s), hl, hs]
    exact integralPointClass_augmentation (s default)
  exact congrArg (fun f => f a) he

theorem integralHomologyZeroAugmentation_class
    (z : LinearMap.ker ((integralChains X).sc' 1 0 0).g.hom) :
    integralHomologyZeroAugmentation X
      (moduleComplexHomologyClass (integralChains X) 1 0 0 (by simp) (by simp) z) =
        integralChainZeroAugmentation X z.val := by
  rw [moduleComplexHomologyClass_eq_cyclesMk]
  have he : (integralChains X).cyclesMk z.val 0 (by simp) z.property =
      ((integralChains X).iCyclesIso 0 0 (by simp) (by simp)).inv z.val := by
    apply (ModuleCat.mono_iff_injective ((integralChains X).iCycles 0)).mp inferInstance
    exact ((integralChains X).i_cyclesMk z.val 0 (by simp) z.property).trans
      (congrArg (fun f => f z.val)
        ((integralChains X).iCyclesIso 0 0 (by simp) (by simp)).inv_hom_id).symm
  rw [he]
  rfl

theorem integralCap_three_augmentation (c : (integralChains X).X 3)
    (phi : (integralCochains X).X 3) :
    integralChainZeroAugmentation X (integralCap 0 3 c phi) =
      (show (integralChains X).X 3 ⟶ integralCoefficient from phi) c := by
  classical
  have hfront : integralFrontFace 0 3 = ContinuousMap.id (integralSimplex 3) := by
    apply ContinuousMap.ext
    intro t
    exact stdSimplex.map_id_apply t
  rw [integral_chain_finite_representation 3 c]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  let a := integralChainCoordinates X 3 c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • integralSingularGenerator s (ULift.up 1) := by
    conv_lhs => rw [ha, map_zsmul]
  change integralChainZeroAugmentation X (integralCap 0 3 (integralSingularGenerator s a) phi) =
    (show (integralChains X).X 3 ⟶ integralCoefficient from phi) (integralSingularGenerator s a)
  rw [hg, integralCap_chain_smul, map_zsmul, map_zsmul, integralCap_generator,
    map_zsmul, integralChainZeroAugmentation_generator, hfront, ContinuousMap.comp_id]
  congr 1
  apply ULift.ext
  simp

theorem integralSupportCap_three_augmentation (A : Set X)
    (c : (integralRelativeChains A).X 3) (phi : (integralRelativeCochains A).X 3) :
    integralChainZeroAugmentation X (integralSupportCap A 0 3 c phi) =
      (show (integralRelativeChains A).X 3 ⟶ integralCoefficient from phi) c := by
  obtain ⟨b, rfl⟩ := integralProjection_surjective (integralSubspaceChains A) 3 c
  rw [integralSupportCap_projection, integralCap_three_augmentation]
  rfl

theorem integralHomologyCohomologyPairing_three_class
    (C : ChainComplex (ModuleCat.{u} Int) Nat)
    (z : LinearMap.ker (C.sc' 4 3 2).g.hom)
    (phi : LinearMap.ker ((integralDualComplex C).sc' 2 3 4).g.hom) :
    integralHomologyCohomologyPairing C 3
      (moduleComplexHomologyClass C 4 3 2 (by simp) (by simp) z)
      (moduleComplexHomologyClass (integralDualComplex C) 2 3 4 (by simp) (by simp) phi) =
        (show C.X 3 ⟶ integralCoefficient from phi.val) z.val := by
  rw [moduleComplexHomologyClass_eq_cyclesMk, moduleComplexHomologyClass_eq_cyclesMk,
    integralHomologyCohomologyPairing_cycles]
  have hz := C.i_cyclesMk z.val 2 (by simp) z.property
  have hp := (integralDualComplex C).i_cyclesMk phi.val 4 (by simp) phi.property
  exact congrArg₂ (fun (f : C.X 3 ⟶ integralCoefficient) (c : C.X 3) => f c) hp hz

theorem integralSupportCapHomologyThree_augmentation (A : Set X)
    (z : integralRelativeHomology A 3) (phi : integralRelativeCohomology A 3) :
    integralHomologyZeroAugmentation X (integralSupportCapHomologyThree A z phi) =
      integralHomologyCohomologyPairing (integralRelativeChains A) 3 z phi := by
  obtain ⟨zc, rfl⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeChains A) 4 3 2 (by simp) (by simp) z
  obtain ⟨pc, rfl⟩ := moduleComplexHomologyClass_surjective
    (integralRelativeCochains A) 2 3 4 (by simp) (by simp) phi
  rw [integralHomologyCohomologyPairing_three_class]
  change integralHomologyZeroAugmentation X
    (integralSupportCapHomologyThree A
      (((integralRelativeChains A).homologyIsoSc' 4 3 2 (by simp) (by simp)).inv
        (moduleHomologyClass _ zc))
      (((integralRelativeCochains A).homologyIsoSc' 2 3 4 (by simp) (by simp)).inv
        (moduleHomologyClass _ pc))) = _
  rw [integralSupportCapHomologyThree_class]
  change integralHomologyZeroAugmentation X
    (moduleComplexHomologyClass (integralChains X) 1 0 0 (by simp) (by simp) _) = _
  rw [integralHomologyZeroAugmentation_class]
  exact integralSupportCap_three_augmentation A zc.val pc.val

end Poincare.Topology
