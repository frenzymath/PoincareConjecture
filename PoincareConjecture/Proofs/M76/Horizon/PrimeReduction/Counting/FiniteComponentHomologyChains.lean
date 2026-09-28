import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ModTwoMayerVietoris
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe u

namespace PoincareConjecture.M76.FiniteComponentHomology

variable {I : Type u} (Y : I → Type u) [∀ i, TopologicalSpace (Y i)]

def singularSigmaCofan : Cofan (fun i => TopCat.toSSet.obj (TopCat.of (Y i))) :=
  Cofan.mk (TopCat.toSSet.obj (TopCat.of (Σ i, Y i)))
    (fun i => TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.sigmaMk i)))

def singularSigmaCofan_isColimit : IsColimit (singularSigmaCofan Y) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨⟨n⟩⟩
  refine (Cofan.isColimitMapCoconeEquiv
    ((evaluation _ (Type u)).obj (Opposite.op ⦋n⦌)) _ (singularSigmaCofan Y)).symm ?_
  change IsColimit (Cofan.mk ((TopCat.toSSet.obj (TopCat.of (Σ i, Y i))) _⦋n⦌)
    (fun i => (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.sigmaMk i))).app _))
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · intro x y h
    have hh := congrArg ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _) h
    have hxy : (⟨x.1, (TopCat.of (Y x.1)).toSSetObjEquiv _ x.2⟩ :
        Σ i, C(Poincare.Topology.integralSimplex n, Y i)) =
        ⟨y.1, (TopCat.of (Y y.1)).toSSetObjEquiv _ y.2⟩ :=
      ContinuousMap.isEmbedding_sigmaMk_comp.injective hh
    exact (Equiv.sigmaCongrRight (fun i =>
      (TopCat.of (Y i)).toSSetObjEquiv (Opposite.op ⦋n⦌))).injective hxy
  · intro s
    obtain ⟨i, t, ht⟩ := ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _ s).exists_lift_sigma
    refine ⟨⟨i, ((TopCat.of (Y i)).toSSetObjEquiv _).symm t⟩, ?_⟩
    apply ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _).injective
    exact ht.symm

theorem chains_preservesCoproducts :
    PreservesColimitsOfShape (Discrete I)
      ((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
        ModTwoMayerVietoris.coefficient : SSet.{u} ⥤ _) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape (Discrete I)
    ((evaluation _ (Type u)).obj (Opposite.op ⦋n⦌) ⋙
      sigmaConst.obj ModTwoMayerVietoris.coefficient)
  infer_instance

def chainsSigmaCofan : Cofan (fun i => ModTwoMayerVietoris.chains (Y i)) :=
  Cofan.mk (ModTwoMayerVietoris.chains (Σ i, Y i))
    (fun i => ModTwoMayerVietoris.chainMap (ContinuousMap.sigmaMk i))

def chainsSigmaCofan_isColimit : IsColimit (chainsSigmaCofan Y) := by
  let := chains_preservesCoproducts (I := I)
  exact isColimitCofanMkObjOfIsColimit
    ((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
      ModTwoMayerVietoris.coefficient) _ _ (singularSigmaCofan_isColimit Y)

variable [Finite I]

def homologySigmaCofan (n : ℕ) : Cofan (fun i => ModTwoMayerVietoris.homology (Y i) n) :=
  Cofan.mk (ModTwoMayerVietoris.homology (Σ i, Y i) n)
    (fun i => ModTwoMayerVietoris.homologyMapOf (ContinuousMap.sigmaMk i) n)

def homologySigmaCofan_isColimit (n : ℕ) : IsColimit (homologySigmaCofan Y n) :=
  isColimitCofanMkObjOfIsColimit (homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) n)
    _ _ (chainsSigmaCofan_isColimit Y)

def homologySigmaIso (n : ℕ) :
    (∐ fun i => ModTwoMayerVietoris.homology (Y i) n) ≅
      ModTwoMayerVietoris.homology (Σ i, Y i) n :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (homologySigmaCofan_isColimit Y n)

@[reassoc]
theorem homologySigmaIso_inclusion (n : ℕ) (i : I) :
    Sigma.ι (fun i => ModTwoMayerVietoris.homology (Y i) n) i ≫
      (homologySigmaIso Y n).hom =
    ModTwoMayerVietoris.homologyMapOf (ContinuousMap.sigmaMk i) n :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom
    (homologySigmaCofan_isColimit Y n) ⟨i⟩

end PoincareConjecture.M76.FiniteComponentHomology
