import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenSubtypeCapNaturality
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenUnionMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMV
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenCapData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]

theorem integralCompactSupportCapTwo_union_difference_square
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace U]
    [LocallyCompactSpace V]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z) :
    integralCompactSupportCapTwo
        (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
        (integralOpenOmegaData (hU.inter hV) omegaY)
        (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY) ≫
      integralOpenUnionHomologyDifference U V 1 =
    integralCompactSupportOpenDifference U V hU hV 2 ≫
      biprod.map
        (integralCompactSupportCapTwo
          (integralOpenSupportDetectedData U hDY hU)
          (integralOpenOmegaData hU omegaY)
          (integralOpenLocalOrientationData hU omegaY hlocalY))
        (integralCompactSupportCapTwo
          (integralOpenSupportDetectedData V hDY hV)
          (integralOpenOmegaData hV omegaY)
          (integralOpenLocalOrientationData hV omegaY hlocalY)) := by
  apply biprod.hom_ext
  · have hn := integralCompactSupportCapTwo_openEmbedding_naturality
        (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
        (integralOpenSupportDetectedData U hDY hU)
        (integralOpenOmegaData (hU.inter hV) omegaY)
        (integralOpenOmegaData hU omegaY)
        (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
        (integralOpenLocalOrientationData hU omegaY hlocalY)
        (integralOpenSubtypeInclusion U V hU)
        (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)
        (integralOpenSubtypeOrientation_inclusion_left U V hU hV hDY omegaY hlocalY)
    have hchain :
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (integralOpenSubtypeInclusion U V hU))) 1 =
          homologyMap (integralNestedChains
            (Set.inter_subset_left : U ∩ V ⊆ U)) 1 := by
      rfl
    rw [hchain] at hn
    simpa [integralOpenUnionHomologyDifference,
      integralCompactSupportOpenDifference, Category.assoc] using hn
  · have hn := integralCompactSupportCapTwo_openEmbedding_naturality
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenSupportDetectedData V hDY hV)
          (integralOpenOmegaData (hU.inter hV) omegaY)
          (integralOpenOmegaData hV omegaY)
          (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
          (integralOpenLocalOrientationData hV omegaY hlocalY)
          (integralOpenSubtypeInclusionRight U V hV)
          (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV)
          (integralOpenSubtypeOrientation_inclusion_right U V hU hV hDY omegaY hlocalY)
    have hchain :
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (integralOpenSubtypeInclusionRight U V hV))) 1 =
          homologyMap (integralNestedChains
            (Set.inter_subset_right : U ∩ V ⊆ V)) 1 := by
      rfl
    rw [hchain] at hn
    have hnneg := congrArg Neg.neg hn
    simpa [integralOpenUnionHomologyDifference,
      integralCompactSupportOpenDifference, Category.assoc,
      Preadditive.neg_comp, Preadditive.comp_neg] using hnneg

end Poincare.Topology
