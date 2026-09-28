import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.FiniteNerveChains










set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology



theorem normalizedIntegralChainMap_fromNormalized {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.normalizedChainComplexMap f integralCoefficient ≫
      B.fromNormalizedChainComplex integralCoefficient =
    A.fromNormalizedChainComplex integralCoefficient ≫
      SSet.chainComplexMap f integralCoefficient := by
  apply (cancel_epi (A.toNormalizedChainComplex integralCoefficient)).mp
  simp only [← Category.assoc, SSet.toNormalizedChainComplex_normalizedChainComplexMap]
  rw [Category.assoc, SSet.toNormalizedChainComplex_fromNormalizedChainComplex,
    SSet.toNormalizedChainComplex_fromNormalizedChainComplex]
  exact SSet.chainComplexMap_PInfty f integralCoefficient

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]




def normalizedSingularComparison {A : SSet.{u}}
    (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X)) :
    A.normalizedChainComplex integralCoefficient.{u} ⟶ integralChains X :=
  A.fromNormalizedChainComplex integralCoefficient ≫
    SSet.chainComplexMap χ integralCoefficient

set_option backward.isDefEq.respectTransparency false in



theorem normalizedSingularComparison_naturality {A B : SSet.{u}}
    (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X))
    (ψ : B ⟶ TopCat.toSSet.obj (TopCat.of Y))
    (a : A ⟶ B) (f : C(X, Y))
    (h : a ≫ ψ = χ ≫ TopCat.toSSet.map (TopCat.ofHom f)) :
    SSet.normalizedChainComplexMap a integralCoefficient ≫
      normalizedSingularComparison ψ =
    normalizedSingularComparison χ ≫ integralChainsFunctor.map (TopCat.ofHom f) := by
  dsimp only [normalizedSingularComparison]
  rw [← Category.assoc, normalizedIntegralChainMap_fromNormalized, Category.assoc]
  change _ = _ ≫ SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) _
  have hm := ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
    integralCoefficient).congr_map h
  simp only [Functor.map_comp] at hm
  simpa only [Category.assoc] using
    congrArg (fun k => A.fromNormalizedChainComplex integralCoefficient ≫ k) hm




theorem normalizedSingularComparison_quasiIso_iff {A : SSet.{u}}
    (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X)) :
    QuasiIso (normalizedSingularComparison χ) ↔
      QuasiIso (SSet.chainComplexMap χ integralCoefficient.{u}) := by
  exact quasiIso_iff_comp_left (A.fromNormalizedChainComplex integralCoefficient)
    (SSet.chainComplexMap χ integralCoefficient)

end PoincareConjecture.Proofs.M59
