import PoincareConjecture.Proofs.M02.Topology.ModuleComplexSingleReduction

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable (A : ModuleCat.{u} Int) (d : Nat)

theorem integralDualSingle_d (i j : Nat) :
    (integralDualComplex ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A)).d
      i j = 0 := by
  ext phi
  change ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A).X i ⟶
    integralCoefficient at phi
  change ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A).d j i ≫ phi = 0
  rw [single_obj_d, zero_comp]

def integralDualSingleDegreeEquiv :
    (((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A).X d ⟶ integralCoefficient.{u})
      ≃ₗ[Int] (A ⟶ integralCoefficient.{u}) where
  toFun phi := (singleObjXSelf (ComplexShape.down Nat) d A).inv ≫ phi
  invFun psi := (singleObjXSelf (ComplexShape.down Nat) d A).hom ≫ psi
  left_inv phi := by simp
  right_inv psi := by simp
  map_add' phi psi := by simp
  map_smul' n phi := by simp only [Linear.comp_smul, RingHom.id_apply]

def integralDualSingleHomologySelfIso :
    (integralDualComplex ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A)).homology d
      ≅ ModuleCat.of Int (A ⟶ integralCoefficient.{u}) :=
  let D := integralDualComplex ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A)
  (D.isoHomologyπ _ d rfl (integralDualSingle_d A d _ _)).symm ≪≫
    D.iCyclesIso d _ rfl (integralDualSingle_d A d _ _) ≪≫
      (integralDualSingleDegreeEquiv A d).toModuleIso

@[reassoc]
theorem integralDualSingleHomologySelfIso_projection :
    (integralDualComplex ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj
      A)).homologyπ d ≫
      (integralDualSingleHomologySelfIso A d).hom =
    (integralDualComplex ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A)).iCycles d ≫
      ModuleCat.ofHom (integralDualSingleDegreeEquiv A d).toLinearMap := by
  simp [integralDualSingleHomologySelfIso]

theorem integralDualSingleHomology_isZero (n : Nat) (hn : n ≠ d) :
    IsZero ((integralDualComplex
      ((single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj A)).homology n) := by
  rw [← exactAt_iff_isZero_homology, exactAt_iff]
  apply ShortComplex.exact_of_isZero_X₂
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun phi psi => ?_⟩
  exact (isZero_single_obj_X (ComplexShape.down Nat) d A n hn).eq_of_src phi psi

variable (C : ChainComplex (ModuleCat.{u} Int) Nat)
  [CategoryTheory.Projective (C.homology d)]
  [∀ n, CategoryTheory.Projective (C.X n)]
  (hC : ∀ n : Nat, n ≠ d → IsZero (C.homology n))

def moduleComplexDualHomologyIso :
    (integralDualComplex C).homology d ≅
      ModuleCat.of Int (C.homology d ⟶ integralCoefficient.{u}) := by
  let := moduleComplexSingleHomologyMap_dual_quasiIso C d hC
  exact asIso (homologyMap (integralDualMap (moduleComplexSingleHomologyMap C d)) d) ≪≫
    integralDualSingleHomologySelfIso (C.homology d) d

include hC in
theorem moduleComplexDualHomology_isZero (n : Nat) (hn : n ≠ d) :
    IsZero ((integralDualComplex C).homology n) := by
  let := moduleComplexSingleHomologyMap_dual_quasiIso C d hC
  exact (integralDualSingleHomology_isZero (C.homology d) d n hn).of_iso
    (asIso (homologyMap (integralDualMap (moduleComplexSingleHomologyMap C d)) n))

@[reassoc]
theorem moduleComplexDualHomologyIso_projection :
    (integralDualComplex C).homologyπ d ≫ (moduleComplexDualHomologyIso d C hC).hom =
      (integralDualComplex C).iCycles d ≫ ModuleCat.ofHom
        (Linear.leftComp Int integralCoefficient
          (moduleComplexHomologySection C d ≫ C.iCycles d)) := by
  dsimp only [moduleComplexDualHomologyIso, Iso.trans_hom, asIso_hom]
  rw [homologyπ_naturality_assoc, integralDualSingleHomologySelfIso_projection,
    ← Category.assoc, cyclesMap_i, Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change (singleObjXSelf (ComplexShape.down Nat) d (C.homology d)).inv ≫
      (moduleComplexSingleHomologyMap C d).f d ≫ phi =
    (moduleComplexHomologySection C d ≫ C.iCycles d) ≫ phi
  rw [moduleComplexSingleHomologyMap, mkHomFromSingle_f]
  simp

end PoincareConjecture.Proofs.M02.Topology
