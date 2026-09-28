import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapNaturality
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientationCompatibility
import PoincareConjecture.Proofs.M02.IntegralOpenCapData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]

theorem integralOpenSubtypeOrientation_inclusion_left
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace U]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (K : Compacts ↥(U ∩ V)) :
    homologyMap (integralSupportEmbeddingChains
      (integralOpenSubtypeInclusion U V hU)
      (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV).injective
      (K : Set ↥(U ∩ V))) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenOmegaData (hU.inter hV) omegaY)
          K (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData U hDY hU)
        (integralOpenOmegaData hU omegaY)
        (K.map (integralOpenSubtypeInclusion U V hU)
          (integralOpenSubtypeInclusion U V hU).continuous)
        (integralOpenLocalOrientationData hU omegaY hlocalY) := by
  refine integralCompactSupportOrientation_openEmbedding
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenSupportDetectedData U hDY hU)
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenOmegaData hU omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
    (integralOpenLocalOrientationData hU omegaY hlocalY)
    (integralOpenSubtypeInclusion U V hU)
    (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV) ?_ K
  intro x
  have hval :
      (integralOpenSubtypeVal U).comp
          (integralOpenSubtypeInclusion U V hU) =
        integralOpenSubtypeVal (U ∩ V) := by
    ext y
    rfl
  have hc := integralOpenOrientation_comp
    (integralOpenSubtypeInclusion U V hU)
    (integralOpenSubtypeVal U)
    (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)
    (integralOpenSubtypeVal_isOpenEmbedding U hU) omegaY x
  have hp := integralOpenOrientation_point
    (integralOpenSubtypeInclusion U V hU)
    (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)
    (integralOpenOmegaData hU omegaY) x
  have hOmega : integralOpenOmegaData (hU.inter hV) omegaY x =
      integralOpenOrientation (integralOpenSubtypeInclusion U V hU)
        (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)
        (integralOpenOmegaData hU omegaY) x := by
    rw [integralOpenOmegaData, integralOpenOmegaData]
    simpa only [hval] using hc
  rw [hOmega]
  simpa [integralOpenOmegaData] using hp

theorem integralOpenSubtypeOrientation_inclusion_right
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace V]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (K : Compacts ↥(U ∩ V)) :
    homologyMap (integralSupportEmbeddingChains
      (integralOpenSubtypeInclusionRight U V hV)
      (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV).injective
      (K : Set ↥(U ∩ V))) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
          (integralOpenOmegaData (hU.inter hV) omegaY)
          K (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData V hDY hV)
        (integralOpenOmegaData hV omegaY)
        (K.map (integralOpenSubtypeInclusionRight U V hV)
          (integralOpenSubtypeInclusionRight U V hV).continuous)
        (integralOpenLocalOrientationData hV omegaY hlocalY) := by
  refine integralCompactSupportOrientation_openEmbedding
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenSupportDetectedData V hDY hV)
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenOmegaData hV omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
    (integralOpenLocalOrientationData hV omegaY hlocalY)
    (integralOpenSubtypeInclusionRight U V hV)
    (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) ?_ K
  intro x
  have hval :
      (integralOpenSubtypeVal V).comp
          (integralOpenSubtypeInclusionRight U V hV) =
        integralOpenSubtypeVal (U ∩ V) := by
    ext y
    rfl
  have hc := integralOpenOrientation_comp
    (integralOpenSubtypeInclusionRight U V hV)
    (integralOpenSubtypeVal V)
    (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV)
    (integralOpenSubtypeVal_isOpenEmbedding V hV) omegaY x
  have hp := integralOpenOrientation_point
    (integralOpenSubtypeInclusionRight U V hV)
    (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV)
    (integralOpenOmegaData hV omegaY) x
  have hOmega : integralOpenOmegaData (hU.inter hV) omegaY x =
      integralOpenOrientation (integralOpenSubtypeInclusionRight U V hV)
        (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV)
        (integralOpenOmegaData hV omegaY) x := by
    rw [integralOpenOmegaData, integralOpenOmegaData]
    simpa only [hval] using hc
  rw [hOmega]
  simpa [integralOpenOmegaData] using hp

theorem integralOpenSubtypeOrientation_union_left
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace U] [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (K : Compacts U) :
    homologyMap (integralSupportEmbeddingChains
      (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV).injective
      (K : Set U)) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData U hDY hU)
          (integralOpenOmegaData hU omegaY)
          K (integralOpenLocalOrientationData hU omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData (hU.union hV) omegaY)
        (K.map (integralOpenSubtypeUnionInclusion U V hU)
          (integralOpenSubtypeUnionInclusion U V hU).continuous)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
  refine integralCompactSupportOrientation_openEmbedding
    (integralOpenSupportDetectedData U hDY hU)
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData hU omegaY)
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData hU omegaY hlocalY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
    (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) ?_ K
  intro x
  have hval :
      (integralOpenSubtypeVal (U ∪ V)).comp
          (integralOpenSubtypeUnionInclusion U V hU) =
        integralOpenSubtypeVal U := by
    rfl
  have hc := integralOpenOrientation_comp
    (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeVal (U ∪ V))
    (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV)
    (integralOpenSubtypeVal_isOpenEmbedding (U ∪ V) (hU.union hV)) omegaY x
  have hp := integralOpenOrientation_point
    (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV)
    (integralOpenOmegaData (hU.union hV) omegaY) x
  have hOmega : integralOpenOmegaData hU omegaY x =
      integralOpenOrientation (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV)
        (integralOpenOmegaData (hU.union hV) omegaY) x := by
    rw [integralOpenOmegaData, integralOpenOmegaData]
    simpa only [hval] using hc
  rw [hOmega]
  simpa [integralOpenOmegaData] using hp

theorem integralOpenSubtypeOrientation_union_right
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
    [LocallyCompactSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace V] [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (K : Compacts V) :
    homologyMap (integralSupportEmbeddingChains
      (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV).injective
      (K : Set V)) 3
        (integralCompactSupportOrientation
          (integralOpenSupportDetectedData V hDY hV)
          (integralOpenOmegaData hV omegaY)
          K (integralOpenLocalOrientationData hV omegaY hlocalY)) =
      integralCompactSupportOrientation
        (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
        (integralOpenOmegaData (hU.union hV) omegaY)
        (K.map (integralOpenSubtypeUnionInclusionRight U V hV)
          (integralOpenSubtypeUnionInclusionRight U V hV).continuous)
        (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY) := by
  refine integralCompactSupportOrientation_openEmbedding
    (integralOpenSupportDetectedData V hDY hV)
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData hV omegaY)
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData hV omegaY hlocalY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
    (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) ?_ K
  intro x
  have hval :
      (integralOpenSubtypeVal (U ∪ V)).comp
          (integralOpenSubtypeUnionInclusionRight U V hV) =
        integralOpenSubtypeVal V := by
    rfl
  have hc := integralOpenOrientation_comp
    (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeVal (U ∪ V))
    (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV)
    (integralOpenSubtypeVal_isOpenEmbedding (U ∪ V) (hU.union hV)) omegaY x
  have hp := integralOpenOrientation_point
    (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV)
    (integralOpenOmegaData (hU.union hV) omegaY) x
  have hOmega : integralOpenOmegaData hV omegaY x =
      integralOpenOrientation (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV)
        (integralOpenOmegaData (hU.union hV) omegaY) x := by
    rw [integralOpenOmegaData, integralOpenOmegaData]
    simpa only [hval] using hc
  rw [hOmega]
  simpa [integralOpenOmegaData] using hp

end PoincareConjecture.Proofs.M02.Topology
