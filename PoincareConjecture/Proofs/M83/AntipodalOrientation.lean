import PoincareConjecture.Proofs.M83.ReflectionLocalHomology
import PoincareConjecture.Proofs.M83.EuclideanOrientation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology



def negation : C(E3, E3) := ⟨fun x => -x, continuous_neg⟩

private theorem negation_puncture (x : E3) :
    MapsTo negation ({x}ᶜ : Set E3) ({-x}ᶜ : Set E3) := by
  intro z hz he
  exact hz (neg_injective he)



theorem negation_reverses_orientation (O : LocalOrientation E3) (x : E3) :
    localHomologyMap negation neg_injective x 3 (O.atPoint x) =
      -O.atPoint (negation x) := by
  have hzero : MapsTo negation ({0}ᶜ : Set E3) ({0}ᶜ : Set E3) := by
    intro z hz he
    exact hz (neg_eq_zero.mp he)
  have hcomp :
      integralRelativeMap (translation x) (translation_puncture x) ≫
        integralRelativeMap negation (negation_puncture x) =
      integralRelativeMap negation hzero ≫
        integralRelativeMap (translation (-x)) (translation_puncture (-x)) := by
    rw [integralRelativeMap_comp, integralRelativeMap_comp]
    congr 1
    ext z : 1
    simp [negation, translation, add_comm]
  have h := congrArg (fun k => (ConcreteCategory.hom (homologyMap k 3))
    (O.atPoint 0)) hcomp
  rw [homologyMap_comp, homologyMap_comp, ModuleCat.comp_apply,
    ModuleCat.comp_apply, translation_preserves_orientation] at h
  have hn : homologyMap (integralRelativeMap negation hzero) 3 =
      -𝟙 (LocalHomology E3 0 3) := neg_relativeHomologyMap
  rw [hn] at h
  change homologyMap (integralRelativeMap negation (negation_puncture x)) 3
      (O.atPoint x) = homologyMap
        (integralRelativeMap (translation (-x)) (translation_puncture (-x))) 3
        (-O.atPoint 0) at h
  rw [map_neg, translation_preserves_orientation] at h
  exact h



theorem negation_pullback (O : LocalOrientation E3) (x : E3) :
    (O.pullback negation (Homeomorph.neg E3).isOpenEmbedding).atPoint x =
      -O.atPoint x := by
  apply (localHomologyEquiv negation (Homeomorph.neg E3).isOpenEmbedding x 3).injective
  change localHomologyMap negation neg_injective x 3 _ =
    localHomologyMap negation neg_injective x 3 _
  rw [LocalOrientation.map_pullback, map_neg, negation_reverses_orientation, neg_neg]

end PoincareConjecture.Proofs.M83
