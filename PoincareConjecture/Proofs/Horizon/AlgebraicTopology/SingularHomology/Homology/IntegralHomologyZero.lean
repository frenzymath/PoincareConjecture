import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralChainCoordinates
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.LinearAlgebra.Finsupp.Pi








set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralHomologyZeroAugmentation (X : Type u) [TopologicalSpace X] :
    integralHomology X 0 ⟶ integralCoefficient :=
  (TopCat.of X).singularHomology₀ε integralCoefficient

def integralPointClass (x : X) : integralCoefficient ⟶ integralHomology X 0 :=
  (integralChains X).liftCycles
    (integralSingularGenerator (ContinuousMap.const (integralSimplex 0) x))
    0 (by simp) (by simp) ≫ (integralChains X).homologyπ 0

theorem integralPointClass_augmentation (x : X) :
    integralPointClass x ≫ integralHomologyZeroAugmentation X = 𝟙 _ := by
  exact (TopCat.toSSet.obj (TopCat.of X)).liftCycles_ιChainComplex_homologyπ_homology₀ε
    integralCoefficient _

theorem integralHomologyZero_hom_ext {M : ModuleCat.{u} Int}
    (f g : integralHomology X 0 ⟶ M)
    (h : ∀ x : X, integralPointClass x ≫ f = integralPointClass x ≫ g) : f = g := by
  let K := integralChains X
  let e := K.iCyclesIso 0 0 (by simp) (by simp)
  apply (cancel_epi (K.homologyπ 0)).mp
  apply (cancel_epi e.inv).mp
  apply SSet.chainComplex_hom_ext
  intro z
  obtain ⟨s, rfl⟩ := ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋0⦌)).symm.surjective z
  have hs : s = ContinuousMap.const (integralSimplex 0) (s default) := by
    ext t
    exact congrArg s (Subsingleton.elim t default)
  have hl : integralSingularGenerator s ≫ e.inv =
      K.liftCycles (integralSingularGenerator s) 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      Category.comp_id, HomologicalComplex.liftCycles_i]
  change integralSingularGenerator s ≫ e.inv ≫ K.homologyπ 0 ≫ f =
    integralSingularGenerator s ≫ e.inv ≫ K.homologyπ 0 ≫ g
  rw [← Category.assoc (integralSingularGenerator s), hl,
    ← Category.assoc (integralSingularGenerator s), hl, hs]
  exact h (s default)

theorem integralPointClass_map (f : C(X, Y)) (x : X) :
    integralPointClass x ≫ HomologicalComplex.homologyMap
        (integralChainsFunctor.map (TopCat.ofHom f)) 0 = integralPointClass (f x) := by
  let F := integralChainsFunctor.map (TopCat.ofHom f)
  let sx := integralSingularGenerator (ContinuousMap.const (integralSimplex 0) x)
  let sy := integralSingularGenerator (ContinuousMap.const (integralSimplex 0) (f x))
  have hs : sx ≫ F.f 0 = sy := by
    exact integralSingularGenerator_map (ContinuousMap.const (integralSimplex 0) x) f
  have hl : (integralChains Y).liftCycles (sx ≫ F.f 0) 0 (by simp)
      (by rw [Category.assoc, F.comm, ← Category.assoc]; simp) =
        (integralChains Y).liftCycles sy 0 (by simp) (by simp) := by
    apply (cancel_mono ((integralChains Y).iCycles 0)).mp
    rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, hs]
  change ((integralChains X).liftCycles sx 0 (by simp) (by simp) ≫
      (integralChains X).homologyπ 0) ≫ HomologicalComplex.homologyMap F 0 =
    (integralChains Y).liftCycles sy 0 (by simp) (by simp) ≫
      (integralChains Y).homologyπ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap, hl]

theorem integralHomologyZeroAugmentation_natural (f : C(X, Y)) :
    HomologicalComplex.homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0 ≫
      integralHomologyZeroAugmentation Y = integralHomologyZeroAugmentation X := by
  apply integralHomologyZero_hom_ext
  intro x
  rw [← Category.assoc, integralPointClass_map,
    integralPointClass_augmentation, integralPointClass_augmentation]

theorem integralHomologyZeroAugmentation_isIso (X : Type u) [TopologicalSpace X]
    [PathConnectedSpace X] : IsIso (integralHomologyZeroAugmentation X) := by
  change IsIso ((TopCat.of X).singularHomology₀ε integralCoefficient)
  infer_instance


def integralHomologyZeroMapKernelIso (f : C(X, Y)) [PathConnectedSpace Y] :
    kernel (HomologicalComplex.homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0) ≅
      kernel (integralHomologyZeroAugmentation X) := by
  let := integralHomologyZeroAugmentation_isIso Y
  exact (kernelCompMono _ (integralHomologyZeroAugmentation Y)).symm ≪≫
    kernelIsoOfEq (integralHomologyZeroAugmentation_natural f)

end Poincare.Topology
