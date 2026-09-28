import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapGlobalD2Induction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapTwoSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapTwoSumSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapThreeDifferenceSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapDifferenceSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMVUnion
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMVIntersection
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenUnionMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenCapData


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology


variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]

theorem integralCompactSupportCapTwo_union_isIso_canonical
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace U] [LocallyCompactSpace V]
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (hD2U : IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData U hDY hU)
      (integralOpenOmegaData hU omegaY)
      (integralOpenLocalOrientationData hU omegaY hlocalY)))
    (hD2V : IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData V hDY hV)
      (integralOpenOmegaData hV omegaY)
      (integralOpenLocalOrientationData hV omegaY hlocalY)))
    (hD2I : IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
      (integralOpenOmegaData (hU.inter hV) omegaY)
      (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)))
    (hD3U : IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData U hDY hU)
      (integralOpenOmegaData hU omegaY)
      (integralOpenLocalOrientationData hU omegaY hlocalY)))
    (hD3V : IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData V hDY hV)
      (integralOpenOmegaData hV omegaY)
      (integralOpenLocalOrientationData hV omegaY hlocalY)))
    (hD3I : IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
      (integralOpenOmegaData (hU.inter hV) omegaY)
      (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY))) :
    IsIso (integralCompactSupportCapTwo
      (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
      (integralOpenOmegaData (hU.union hV) omegaY)
      (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) := by
  let d2U := integralCompactSupportCapTwo
    (integralOpenSupportDetectedData U hDY hU)
    (integralOpenOmegaData hU omegaY)
    (integralOpenLocalOrientationData hU omegaY hlocalY)
  let d2V := integralCompactSupportCapTwo
    (integralOpenSupportDetectedData V hDY hV)
    (integralOpenOmegaData hV omegaY)
    (integralOpenLocalOrientationData hV omegaY hlocalY)
  let d2I := integralCompactSupportCapTwo
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
  let d3U := integralCompactSupportCapThree
    (integralOpenSupportDetectedData U hDY hU)
    (integralOpenOmegaData hU omegaY)
    (integralOpenLocalOrientationData hU omegaY hlocalY)
  let d3V := integralCompactSupportCapThree
    (integralOpenSupportDetectedData V hDY hV)
    (integralOpenOmegaData hV omegaY)
    (integralOpenLocalOrientationData hV omegaY hlocalY)
  let d3I := integralCompactSupportCapThree
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
  let cDiff2 := integralCompactSupportOpenDifference U V hU hV 2
  let cSum2 := integralCompactSupportOpenSum U V hU hV 2
  let cConn2 := integralCompactSupportOpenConnecting U V hU hV 2
  let cDiff3 := integralCompactSupportOpenDifference U V hU hV 3
  let hDiff1 := integralOpenUnionHomologyDifference U V 1
  let hSum1 := integralOpenUnionHomologySum U V 1
  let hConn1 := integralOpenUnionHomologyConnectingToIntersection U V hU hV 0
  let hDiff0 := integralOpenUnionHomologyDifference U V 0
  let d2Pair := biprod.map d2U d2V
  let d3Pair := biprod.map d3U d3V
  let d2Union := integralCompactSupportCapTwo
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
  let : IsIso d2U := hD2U
  let : IsIso d2V := hD2V
  let : IsIso d2I := hD2I
  let : IsIso d3U := hD3U
  let : IsIso d3V := hD3V
  let : IsIso d3I := hD3I
  let : IsIso d2Pair := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · apply (ModuleCat.mono_iff_injective _).mp
      infer_instance
    · apply (ModuleCat.epi_iff_surjective _).mp
      infer_instance
  let : IsIso d3Pair := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · apply (ModuleCat.mono_iff_injective _).mp
      infer_instance
    · apply (ModuleCat.epi_iff_surjective _).mp
      infer_instance
  apply integralCompactSupportCapTwo_union_isIso_of_squares U V hU hV
    cDiff2 cSum2 cConn2 cDiff3 hDiff1 hSum1 hConn1 hDiff0 d2I d2Pair d2Union
    (integralCompactSupportCapThree
      (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
      (integralOpenOmegaData (hU.inter hV) omegaY)
      (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)) d3Pair
  · intro a
    exact congrArg (fun f => f.hom a)
      (integralCompactSupportOpenDifference_sum U V hU hV 2)
  · intro y
    have h := congrArg (fun f => f.hom y)
      (integralOpenUnionHomologyConnecting_difference U V hU hV 0)
    change (integralOpenUnionHomologyDifference U V 0).hom
        ((integralOpenUnionHomologyConnectingToIntersection U V hU hV 0).hom y) = 0 at h
    exact h
  · intro a
    have h := congrArg (fun f => f.hom a)
      (integralCompactSupportCapTwo_union_difference_square U V hU hV hDY omegaY hlocalY)
    simpa [d2Pair, d2I, cDiff2, hDiff1] using h.symm
  · intro v
    exact congrArg (fun f => f.hom v)
      (integralCompactSupportCapTwo_union_sum_square U V hU hV hDY omegaY hlocalY)
  · intro x
    have h := congrArg (fun f => f.hom x)
      (integralCompactSupportCapTwo_union_connecting_square U V hU hV hDY omegaY hlocalY)
    simpa [d2Union, d3I, cConn2, hConn1] using h
  · intro z
    have h := congrArg (fun f => f.hom z)
      (integralCompactSupportCapThree_union_difference_square U V hU hV hDY omegaY hlocalY)
    simpa [d3Pair, d3I, cDiff3, hDiff0] using h.symm
  · intro x hx
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralCompactSupportOpenMayerVietoris_exact_union U V hU hV 2) x hx
    exact ⟨w, hw⟩
  · intro z hz
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralCompactSupportOpenMayerVietoris_exact_intersection U V hU hV 2) z hz
    exact ⟨x, hx⟩
  · intro y hy
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralOpenUnionHomologyMayerVietoris_exact_union U V hU hV 0) y hy
    exact ⟨w, hw⟩
  · intro w hw
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralOpenUnionHomologyMayerVietoris_exact U V hU hV 1) w hw
    exact ⟨z, hz⟩

end Poincare.Topology
