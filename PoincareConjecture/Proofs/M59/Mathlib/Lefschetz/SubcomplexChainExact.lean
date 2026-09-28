import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe u v w

namespace SSet

variable {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  (R : C)

theorem chainComplexFunctor_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan ((chainComplexFunctor C).obj R :
      SSet.{u} ⥤ ChainComplex C ℕ) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape WalkingSpan
    ((evaluation _ (Type u)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R)
  infer_instance

variable {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B)

set_option backward.isDefEq.respectTransparency false in

theorem chainComplexMap_subcomplex_mono_f (n : ℕ) :
    Mono ((chainComplexMap (Subcomplex.homOfLE h) R).f n) := by
  classical
  let c : Cofan (fun _ : B.obj (Opposite.op ⦋n⦌) => R) :=
    Cofan.mk ((A.toSSet.chainComplex R).X n)
      (fun b => if hb : b.val ∈ A.obj _ then A.toSSet.ιChainComplex ⟨b.val, hb⟩ else 0)
  let r := (B.toSSet.isColimitChainComplexXCofan R n).desc c
  have hr : (chainComplexMap (Subcomplex.homOfLE h) R).f n ≫ r = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro a
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    have hf := (B.toSSet.isColimitChainComplexXCofan R n).fac c
      (Discrete.mk ((Subcomplex.homOfLE h).app _ a))
    change B.toSSet.ιChainComplex ((Subcomplex.homOfLE h).app _ a) ≫ r = _ at hf
    simp only [c, Cofan.mk_ι_app, Subcomplex.homOfLE_app_val,
      dif_pos a.property] at hf
    rw [Category.comp_id]
    refine hf.trans ?_
    apply congrArg (fun b : A.toSSet _⦋n⦌ => A.toSSet.ιChainComplex (R := R) b)
    exact Subtype.ext rfl
  exact mono_of_mono_fac hr

theorem chainComplexMap_subcomplex_mono :
    Mono (chainComplexMap (Subcomplex.homOfLE h) R) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact chainComplexMap_subcomplex_mono_f R h n

variable {A₁ A₂ A₃ A₄ : X.Subcomplex}

theorem chainComplex_subcomplex_isPushout
    (sq : Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (chainComplexMap (Subcomplex.homOfLE sq.le₁₂) R)
      (chainComplexMap (Subcomplex.homOfLE sq.le₁₃) R)
      (chainComplexMap (Subcomplex.homOfLE sq.le₂₄) R)
      (chainComplexMap (Subcomplex.homOfLE sq.le₃₄) R) := by
  let := chainComplexFunctor_preservesPushouts R
  exact sq.isPushout.map ((chainComplexFunctor C).obj R)

theorem chainComplex_subcomplex_shortExact
    (sq : Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    (chainComplex_subcomplex_isPushout R sq).shortComplex.ShortExact := by
  let hp := chainComplex_subcomplex_isPushout R sq
  let := chainComplexMap_subcomplex_mono R sq.le₁₂
  exact { exact := hp.exact_shortComplex, mono_f := by
            dsimp only [CommSq.shortComplex]
            infer_instance
          epi_g := hp.epi_shortComplex_g }

end SSet
