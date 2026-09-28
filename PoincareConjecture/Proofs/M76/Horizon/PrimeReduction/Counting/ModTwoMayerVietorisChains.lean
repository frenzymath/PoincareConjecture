import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FiniteComplexHomologyCoefficients
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenMayerVietoris
import Mathlib.LinearAlgebra.Finsupp.VectorSpace









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open Poincare.Topology
open scoped Simplicial

universe u v

namespace PoincareConjecture.M76.ModTwoMayerVietoris

variable {X : Type u} [TopologicalSpace X]

theorem smallChains_projective {I : Type v} (U : I → Set X) (n : ℕ) :
    Projective ((integralSmallChainComplex U).X n) := by
  classical
  have hli : LinearIndependent ℤ (fun s : C(integralSimplex n, X) =>
      integralSingularGenerator s (ULift.up 1)) := by
    apply LinearIndependent.of_comp (integralChainCoordinates X n).toLinearMap
    change LinearIndependent ℤ (fun s : C(integralSimplex n, X) =>
      integralChainCoordinates X n (integralSingularGenerator s (ULift.up 1)))
    have he : (fun s : C(integralSimplex n, X) =>
        integralChainCoordinates X n (integralSingularGenerator s (ULift.up 1))) =
        (fun s => Finsupp.single s (ULift.up 1 : ULift.{u} ℤ)) :=
      funext (fun s => integralChainCoordinates_generator s (ULift.up 1))
    rw [he]
    exact (Finsupp.linearIndependent_single_of_ne_zero (R := ℤ)
        (v := fun _ : C(integralSimplex n, X) => (ULift.up 1 : ULift.{u} ℤ))
        (fun _ h => by have := congrArg ULift.down h; exact one_ne_zero this))
  exact ModuleCat.projective_of_free
    (Module.Basis.span (hli.comp Subtype.val Subtype.val_injective))

abbrev coefficientChange : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} (ZMod 2) :=
  ModuleCat.extendScalars (Int.castRingHom (ZMod 2))

instance coefficientChange_additive : (coefficientChange.{u}).Additive := by
  constructor
  intro M N f g
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (ModuleCat.extendScalars (Int.castRingHom (ZMod 2))).map (f + g) _ =
    (ModuleCat.extendScalars (Int.castRingHom (ZMod 2))).map f _ +
    (ModuleCat.extendScalars (Int.castRingHom (ZMod 2))).map g _
  simp only [ModuleCat.ExtendScalars.map_tmul]
  let : Module ℤ (ZMod 2) := Module.compHom (ZMod 2) (Int.castRingHom (ZMod 2))
  exact TensorProduct.tmul_add _ _ _

abbrev chainChange := (coefficientChange.{u}).mapHomologicalComplex (ComplexShape.down ℕ)

def openChainSequence (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ) :=
  (integralOpenChainSequence A B).map chainChange

theorem openChainSequence_shortExact (A B : Set X) :
    (openChainSequence A B).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let := smallChains_projective (integralBinaryCover A B) n
  have hS := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (integralOpenChainSequence_shortExact A B) n
  let : Projective ((integralOpenChainSequence A B).map
      (HomologicalComplex.eval _ _ n)).X₃ := smallChains_projective _ n
  exact (hS.splittingOfProjective.map coefficientChange).shortExact

theorem openComparison_quasiIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    QuasiIso (chainChange.map
      (integralSmallChainInclusion (integralBinaryCover A B))) := by
  let := smallChains_projective (integralBinaryCover A B)
  let : ∀ n, Projective ((integralChains X).X n) := fun n =>
    FiniteComplexHomology.integralChains_projective
      (TopCat.toSSet.obj (TopCat.of X)) n
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective
    (integralSmallChainInclusion (integralBinaryCover A B))).mp
      (integralOpenComparison_quasiIso A B hA hB hcover)
  rw [← he]
  exact (coefficientChange.mapHomotopyEquiv e).quasiIso_hom

abbrev coefficient : ModuleCat.{u} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))

abbrev chains (Y : Type u) [TopologicalSpace Y] :
    ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ :=
  (TopCat.toSSet.obj (TopCat.of Y)).chainComplex coefficient.{u}

def chainIso (Y : Type u) [TopologicalSpace Y] :
    chains Y ≅ chainChange.obj (integralChains Y) :=
  (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).mapIso
    FiniteComplexHomology.modTwoCoefficientIso).app
      (TopCat.toSSet.obj (TopCat.of Y))).symm ≪≫
    FiniteComplexHomology.chainCoefficientIso coefficientChange
      (TopCat.toSSet.obj (TopCat.of Y)) integralCoefficient

theorem chainCoefficientIso_naturality {S T : SSet.{u}} (f : S ⟶ T) :
    SSet.chainComplexMap f (coefficientChange.obj integralCoefficient) ≫
      (FiniteComplexHomology.chainCoefficientIso coefficientChange T integralCoefficient).hom =
    (FiniteComplexHomology.chainCoefficientIso coefficientChange S integralCoefficient).hom ≫
      chainChange.map (SSet.chainComplexMap f integralCoefficient) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  intro x
  change S.ιChainComplex x ≫ (SSet.chainComplexMap f _).f n ≫
    sigmaComparison coefficientChange (fun _ : T _⦋n⦌ => integralCoefficient) =
    S.ιChainComplex x ≫ sigmaComparison coefficientChange
      (fun _ : S _⦋n⦌ => integralCoefficient) ≫
        coefficientChange.map ((SSet.chainComplexMap f integralCoefficient).f n)
  rw [SSet.ι_chainComplexMap_f_assoc]
  change Sigma.ι (fun _ : T _⦋n⦌ => coefficientChange.obj integralCoefficient) _ ≫
    sigmaComparison coefficientChange _ =
    Sigma.ι (fun _ : S _⦋n⦌ => coefficientChange.obj integralCoefficient) _ ≫
      sigmaComparison coefficientChange _ ≫ _
  simp only [ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc, ← Functor.map_comp]
  congr 1
  change T.ιChainComplex _ = S.ιChainComplex x ≫
    (SSet.chainComplexMap f integralCoefficient).f n
  rw [SSet.ι_chainComplexMap_f]

abbrev chainMap {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) : chains Y ⟶ chains Z :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) coefficient

@[reassoc]
theorem chainIso_naturality {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) :
    chainMap f ≫ (chainIso Z).hom =
      (chainIso Y).hom ≫ chainChange.map (integralChainsFunctor.map (TopCat.ofHom f)) := by
  let t := ((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).mapIso
    FiniteComplexHomology.modTwoCoefficientIso).inv
  have ht := t.naturality (TopCat.toSSet.map (TopCat.ofHom f))
  dsimp only [chainIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc]
  change chainMap f ≫ t.app _ ≫ _ = t.app _ ≫ _ ≫ _
  rw [← Category.assoc, ht, Category.assoc, chainCoefficientIso_naturality]
  rfl

end PoincareConjecture.M76.ModTwoMayerVietoris
