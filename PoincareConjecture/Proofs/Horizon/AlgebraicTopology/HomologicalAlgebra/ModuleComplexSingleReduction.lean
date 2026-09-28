import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCohomologyExcision
import Mathlib.Algebra.Homology.SingleHomology









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable (C : ChainComplex (ModuleCat.{u} Int) Nat) (d : Nat)
  [CategoryTheory.Projective (C.homology d)]

def moduleComplexHomologySection : C.homology d ⟶ C.cycles d :=
  CategoryTheory.Projective.factorThru (𝟙 (C.homology d)) (C.homologyπ d)

@[reassoc (attr := simp)]
theorem moduleComplexHomologySection_projection :
    moduleComplexHomologySection C d ≫ C.homologyπ d = 𝟙 _ :=
  CategoryTheory.Projective.factorThru_comp _ _

def moduleComplexSingleHomologyMap :
    (HomologicalComplex.single (ModuleCat.{u} Int) (ComplexShape.down Nat) d).obj
      (C.homology d) ⟶ C :=
  mkHomFromSingle (moduleComplexHomologySection C d ≫ C.iCycles d) (by
    intro k hk
    rw [Category.assoc, C.iCycles_d, comp_zero])

theorem moduleComplexSingleHomologyMap_cycles :
    cyclesMap (moduleComplexSingleHomologyMap C d) d =
      (singleObjCyclesSelfIso (ComplexShape.down Nat) d (C.homology d)).hom ≫
        moduleComplexHomologySection C d := by
  apply (cancel_mono (C.iCycles d)).mp
  rw [cyclesMap_i]
  change _ = (singleObjCyclesSelfIso (ComplexShape.down Nat) d (C.homology d)).hom ≫
    moduleComplexHomologySection C d ≫ C.iCycles d
  rw [moduleComplexSingleHomologyMap, mkHomFromSingle_f,
    singleObjCyclesSelfIso_hom, Category.assoc]

theorem moduleComplexSingleHomologyMap_homology :
    homologyMap (moduleComplexSingleHomologyMap C d) d =
      (singleObjHomologySelfIso (ComplexShape.down Nat) d (C.homology d)).hom := by
  apply (cancel_epi (((HomologicalComplex.single (ModuleCat.{u} Int)
    (ComplexShape.down Nat) d).obj (C.homology d)).homologyπ d)).mp
  rw [homologyπ_naturality, moduleComplexSingleHomologyMap_cycles,
    Category.assoc, moduleComplexHomologySection_projection, Category.comp_id,
    homologyπ_singleObjHomologySelfIso_hom]

theorem moduleComplexSingleHomologyMap_quasiIso
    (hC : ∀ n : Nat, n ≠ d → IsZero (C.homology n)) :
    QuasiIso (moduleComplexSingleHomologyMap C d) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n = d
  · subst n
    rw [moduleComplexSingleHomologyMap_homology]
    infer_instance
  · exact (isZero_single_obj_homology (ComplexShape.down Nat) d (C.homology d) n hn).isIso
      (hC n hn) _

theorem moduleComplexSingleHomologyMap_dual_quasiIso
    [∀ n, CategoryTheory.Projective (C.X n)]
    (hC : ∀ n : Nat, n ≠ d → IsZero (C.homology n)) :
    QuasiIso (integralDualMap (moduleComplexSingleHomologyMap C d)) :=
  integralDualMap_quasiIso_of_projective _ (moduleComplexSingleHomologyMap_quasiIso C d hC)

end Poincare.Topology
