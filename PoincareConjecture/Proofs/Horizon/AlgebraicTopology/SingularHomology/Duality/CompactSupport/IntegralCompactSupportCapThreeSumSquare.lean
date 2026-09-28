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

theorem integralCompactSupportCapThree_union_sum_square
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace U] [LocallyCompactSpace V]
    [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z) :
    integralCompactSupportOpenSum U V hU hV 3 ≫
        integralCompactSupportCapThree
          (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
          (integralOpenOmegaData (hU.union hV) omegaY)
          (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) =
      biprod.map
        (integralCompactSupportCapThree
          (integralOpenSupportDetectedData U hDY hU)
          (integralOpenOmegaData hU omegaY)
          (integralOpenLocalOrientationData hU omegaY hlocalY))
        (integralCompactSupportCapThree
          (integralOpenSupportDetectedData V hDY hV)
          (integralOpenOmegaData hV omegaY)
          (integralOpenLocalOrientationData hV omegaY hlocalY)) ≫
      integralOpenUnionHomologySum U V 0 := by
  apply biprod.hom_ext'
  · have hn := integralCompactSupportCapThree_openEmbedding_naturality
        (integralOpenSupportDetectedData U hDY hU)
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData hU omegaY)
        (integralOpenOmegaData (hU.union hV) omegaY)
        (integralOpenLocalOrientationData hU omegaY hlocalY)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
        (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV)
        (integralOpenSubtypeOrientation_union_left U V hU hV hDY omegaY hlocalY)
    have hchain :
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (integralOpenSubtypeUnionInclusion U V hU))) 0 =
          homologyMap (integralNestedChains
            (Set.subset_union_left : U ⊆ U ∪ V)) 0 := by
      rfl
    rw [hchain] at hn
    simpa [integralCompactSupportOpenSum, integralOpenUnionHomologySum,
      Category.assoc] using hn.symm
  · have hn := integralCompactSupportCapThree_openEmbedding_naturality
        (integralOpenSupportDetectedData V hDY hV)
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData hV omegaY)
        (integralOpenOmegaData (hU.union hV) omegaY)
        (integralOpenLocalOrientationData hV omegaY hlocalY)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
        (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV)
        (integralOpenSubtypeOrientation_union_right U V hU hV hDY omegaY hlocalY)
    have hchain :
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (integralOpenSubtypeUnionInclusionRight U V hV))) 0 =
          homologyMap (integralNestedChains
            (Set.subset_union_right : V ⊆ U ∪ V)) 0 := by
      rfl
    rw [hchain] at hn
    simpa [integralCompactSupportOpenSum, integralOpenUnionHomologySum,
      Category.assoc] using hn.symm

end Poincare.Topology
