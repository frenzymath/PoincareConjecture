import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Data.ZMod.Basic
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.FiniteNerveChains

/-!
# Coefficient change for actual simplicial chains

Coproduct-preserving additive functors commute with simplicial chains.
This permits changing coefficients in an actual chain homotopy equivalence,
without requiring the coefficient-change functor to be exact.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe w v u v' u'

namespace PoincareMT.M76.FiniteComplexHomology

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F]

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient-change comparison in every simplicial degree. -/
def chainCoefficientIso (X : SSet.{w}) (A : C) :
    X.chainComplex (F.obj A) ≅ (F.mapHomologicalComplex _).obj (X.chainComplex A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => asIso (sigmaComparison F (fun _ : X _⦋n⦌ => A))) (by
      rintro i j (rfl : j + 1 = i)
      apply SSet.chainComplex_hom_ext
      intro x
      symm
      simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp,
        Preadditive.zsmul_comp]
      change (∑ k : Fin (j + 2), (-1 : ℤ) ^ k.val •
        (Sigma.ι (fun _ : X _⦋j⦌ => F.obj A) (X.δ k x) ≫
          sigmaComparison F (fun _ : X _⦋j⦌ => A))) =
        Sigma.ι (fun _ : X _⦋j + 1⦌ => F.obj A) x ≫
          sigmaComparison F (fun _ : X _⦋j + 1⦌ => A) ≫
            F.map ((X.chainComplex A).d (j + 1) j)
      simp only [ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc, ← F.map_comp]
      change (∑ k : Fin (j + 2), (-1 : ℤ) ^ k.val •
        F.map (X.ιChainComplex (R := A) (X.δ k x))) =
        F.map (X.ιChainComplex x ≫ (X.chainComplex A).d (j + 1) j)
      rw [SSet.ιChainComplex_d, F.map_sum]
      simp only [F.map_zsmul])

/-- Coefficient change carries a constructed simplicial chain homotopy
equivalence to another actual chain homotopy equivalence. -/
def changeChainHomotopyEquiv {X Y : SSet.{w}} (A : C)
    (e : HomotopyEquiv (X.chainComplex A) (Y.chainComplex A)) :
    HomotopyEquiv (X.chainComplex (F.obj A)) (Y.chainComplex (F.obj A)) :=
  ((HomotopyEquiv.ofIso (chainCoefficientIso F X A)).trans (F.mapHomotopyEquiv e)).trans
    (HomotopyEquiv.ofIso (chainCoefficientIso F Y A).symm)

/-- Simplicial chains are the literal finitely supported coefficient families. -/
def chainCoordinates {R : Type*} [CommRing R] (X : SSet.{w}) (A : ModuleCat.{w} R) (n : ℕ) :
    (X.chainComplex A).X n ≃ₗ[R] (X _⦋n⦌ →₀ A) :=
  ((X.isColimitChainComplexXCofan A n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit R A (X _⦋n⦌))).toLinearEquiv

/-- Integral simplicial chains are projective in every degree. -/
theorem integralChains_projective (X : SSet.{w}) (n : ℕ) :
    Projective ((X.chainComplex PoincareMT.Proofs.M02.Topology.integralCoefficient.{w}).X n) := by
  let e := chainCoordinates X PoincareMT.Proofs.M02.Topology.integralCoefficient.{w} n
  let : Module.Free ℤ ((X.chainComplex
    PoincareMT.Proofs.M02.Topology.integralCoefficient.{w}).X n) :=
      Module.Free.of_equiv e.symm
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis ℤ
    ((X.chainComplex PoincareMT.Proofs.M02.Topology.integralCoefficient.{w}).X n))

/-- A finite simplicial degree and finite coefficient module give a finite chain module. -/
theorem chainModuleFinite {R : Type*} [CommRing R] (X : SSet.{w}) (A : ModuleCat.{w} R)
    [Module.Finite R A] (n : ℕ) [Finite (X _⦋n⦌)] :
    Module.Finite R ((X.chainComplex A).X n) := by
  let := Fintype.ofFinite (X _⦋n⦌)
  exact Module.Finite.equiv (chainCoordinates X A n).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Extension of integral unit coefficients is the actual mod-two coefficient module. -/
def modTwoCoefficientIso :
    (ModuleCat.extendScalars (Int.castRingHom (ZMod 2))).obj
      PoincareMT.Proofs.M02.Topology.integralCoefficient.{w} ≅
      ModuleCat.of (ZMod 2) (ULift.{w} (ZMod 2)) := by
  apply LinearEquiv.toModuleIso
  -- Extension of scalars uses an integer action equal to the canonical one by uniqueness.
  convert! (((TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (ZMod 2) (ZMod 2))
    (ULift.moduleEquiv : ULift.{w} ℤ ≃ₗ[ℤ] ℤ)).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ (ZMod 2) (ZMod 2))).trans
        (ULift.moduleEquiv : ULift.{w} (ZMod 2) ≃ₗ[ZMod 2] ZMod 2).symm) using 1 <;>
    try rfl
  all_goals congr 1 <;> try rfl
  all_goals
    first
    | exact Subsingleton.elim _ _
    | congr 2; try rfl
  all_goals
    first
    | exact Subsingleton.elim _ _
    | exact proof_irrel_heq _ _

set_option backward.isDefEq.respectTransparency false in
/-- An integral comparison of actual simplicial chains constructs a
mod-two chain homotopy equivalence, using projectivity before changing coefficients. -/
theorem modTwo_homotopyEquiv_of_integral_quasiIso {X Y : SSet.{w}} (f : X ⟶ Y)
    (hf : QuasiIso (SSet.chainComplexMap f
      PoincareMT.Proofs.M02.Topology.integralCoefficient.{w})) :
    Nonempty (HomotopyEquiv
      (X.chainComplex (ModuleCat.of (ZMod 2) (ULift.{w} (ZMod 2))))
      (Y.chainComplex (ModuleCat.of (ZMod 2) (ULift.{w} (ZMod 2))))) := by
  let := integralChains_projective X
  let := integralChains_projective Y
  obtain ⟨e, _⟩ := (ChainComplex.quasiIso_iff_of_projective
    (SSet.chainComplexMap f PoincareMT.Proofs.M02.Topology.integralCoefficient.{w})).mp hf
  let F : ModuleCat.{w} ℤ ⥤ ModuleCat.{w} (ZMod 2) :=
    ModuleCat.extendScalars (Int.castRingHom (ZMod 2))
  let : F.Additive := by
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
  let e' := changeChainHomotopyEquiv F _ e
  let eX := ((SSet.chainComplexFunctor (ModuleCat.{w} (ZMod 2))).mapIso
    modTwoCoefficientIso).app X
  let eY := ((SSet.chainComplexFunctor (ModuleCat.{w} (ZMod 2))).mapIso
    modTwoCoefficientIso).app Y
  exact ⟨((HomotopyEquiv.ofIso eX.symm).trans e').trans (HomotopyEquiv.ofIso eY)⟩

end PoincareMT.M76.FiniteComplexHomology
