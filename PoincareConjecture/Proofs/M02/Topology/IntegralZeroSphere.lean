import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyZero
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02.Topology

private def integralPairSum :
    ModuleCat.of Int (Bool → ULift.{u} Int) ⟶ integralCoefficient :=
  ModuleCat.ofHom
    ((LinearMap.proj false : (Bool → ULift.{u} Int) →ₗ[Int] ULift.{u} Int) +
      LinearMap.proj true)

private def integralPairSumKernelIso : kernel integralPairSum.{u} ≅ integralCoefficient := by
  let e : LinearMap.ker integralPairSum.{u}.hom ≃ₗ[Int] ULift.{u} Int :=
    { toFun := fun z => z.val false
      invFun := fun a => ⟨fun b => if b then -a else a, by
        change a + -a = 0
        exact add_neg_cancel a⟩
      left_inv := by
        intro z
        apply Subtype.ext
        funext b
        cases b
        · rfl
        · have hz : z.val false + z.val true = 0 := z.property
          have ht : z.val true = -z.val false := by
            simpa using congrArg (fun a => a - z.val false) hz
          exact ht.symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ModuleCat.kernelIsoKer integralPairSum ≪≫ e.toModuleIso

def integralTwoComponentsAugmentationKernelIso
    (X : Type u) [TopologicalSpace X] (e : ZerothHomotopy X ≃ Bool) :
    kernel (integralHomologyZeroAugmentation X) ≅ integralCoefficient := by
  classical
  let Q : ZerothHomotopy X → ModuleCat.{u} Int := fun _ => integralCoefficient
  let eS : (∐ Q) ≅ ModuleCat.of Int (ZerothHomotopy X →₀ ULift.{u} Int) :=
    colimit.isoColimitCocone
      ⟨_, ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (ZerothHomotopy X)⟩
  let eF : ModuleCat.of Int (ZerothHomotopy X →₀ ULift.{u} Int) ≅
      ModuleCat.of Int (Bool → ULift.{u} Int) :=
    ((Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) e).trans
      (Finsupp.linearEquivFunOnFinite Int (ULift.{u} Int) Bool)).toModuleIso
  let eH := (TopCat.of X).singularHomology₀Iso integralCoefficient
  let E := eH ≪≫ eS ≪≫ eF
  have hsum : eS.hom ≫ eF.hom ≫ integralPairSum = Sigma.desc (fun _ => 𝟙 integralCoefficient) := by
    apply Sigma.hom_ext
    intro i
    have hi : Sigma.ι Q i ≫ eS.hom =
        ModuleCat.ofHom (Finsupp.lsingle i (R := Int) (M := ULift.{u} Int)) :=
      colimit.isoColimitCocone_ι_hom _ _
    rw [← Category.assoc, hi, Sigma.ι_desc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ((Finsupp.linearEquivFunOnFinite Int (ULift.{u} Int) Bool)
        ((Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) e) (Finsupp.single i a))) false +
      ((Finsupp.linearEquivFunOnFinite Int (ULift.{u} Int) Bool)
        ((Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) e) (Finsupp.single i a))) true = a
    rw [Finsupp.domLCongr_single, Finsupp.linearEquivFunOnFinite_single]
    cases e i <;> simp
  have hE : integralHomologyZeroAugmentation X ≫ (Iso.refl integralCoefficient).hom =
      E.hom ≫ integralPairSum := by
    rw [Iso.refl_hom, Category.comp_id]
    change integralHomologyZeroAugmentation X = (eH.hom ≫ eS.hom ≫ eF.hom) ≫ integralPairSum
    rw [Category.assoc, Category.assoc, hsum]
    exact ((TopCat.of X).singularHomology₀Iso_sigma_desc_id integralCoefficient).symm
  exact kernel.mapIso _ _ E (Iso.refl _) hE ≪≫ integralPairSumKernelIso

private def integralZerothHomotopyEquivOfTotallyDisconnected
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    ZerothHomotopy X ≃ X where
  toFun := ZerothHomotopy.lift id (by
    intro x y p
    have h := TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1
    simpa using h)
  invFun := ZerothHomotopy.mk
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective q
    rfl
  right_inv := fun _ => rfl

private def integralRealUnitSphereEquivBool : Metric.sphere (0 : Real) 1 ≃ Bool where
  toFun x := if x.val = 1 then true else false
  invFun b := ⟨if b then 1 else -1, by cases b <;> simp⟩
  left_inv x := by
    have hxnorm : |x.val| = 1 := by
      have hx : dist x.val (0 : Real) = 1 := x.property
      rw [Real.dist_eq, sub_zero] at hx
      exact hx
    have hx : x.val = 1 ∨ x.val = -1 := abs_eq_abs.mp (by simpa using hxnorm)
    apply Subtype.ext
    rcases hx with hx | hx <;> norm_num [hx]
  right_inv b := by cases b <;> norm_num

private def integralZeroSphereEquivBool :
    Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1 ≃ Bool := by
  let e := (OrthonormalBasis.singleton (Fin 1) Real).repr.symm
  let eS : Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1 ≃ Metric.sphere (0 : Real) 1 :=
    e.toEquiv.subtypeEquiv (fun x => by
      simp only [Metric.mem_sphere, dist_zero_right]
      change (‖x‖ = 1) ↔ ‖e x‖ = 1
      rw [e.norm_map]
      rfl)
  exact eS.trans integralRealUnitSphereEquivBool

def integralZeroSphereAugmentationKernelIso :
    kernel (integralHomologyZeroAugmentation
      (Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1)) ≅ integralCoefficient := by
  let S := Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1
  let : Finite S := Finite.of_equiv Bool integralZeroSphereEquivBool.symm
  exact integralTwoComponentsAugmentationKernelIso S
    ((integralZerothHomotopyEquivOfTotallyDisconnected S).trans integralZeroSphereEquivBool)

end PoincareConjecture.Proofs.M02.Topology
