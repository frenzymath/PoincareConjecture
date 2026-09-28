import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapD3UnionInduction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapThreeDifferenceSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapThreeSumSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMVUnion
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Homology.IntegralOpenUnionHomologyTerminal
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenUnionMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenCapData


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology


variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]

theorem integralCompactSupportCapThree_union_isIso_canonical
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace U] [LocallyCompactSpace V]
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
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
      (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)))
    (hC4 : IsZero (integralCompactSupportCohomology (↥(U ∩ V)) 4)) :
    IsIso (integralCompactSupportCapThree
      (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
      (integralOpenOmegaData (hU.union hV) omegaY)
      (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) := by
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
  let d3Union := integralCompactSupportCapThree
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
  let cDiff3 := integralCompactSupportOpenDifference U V hU hV 3
  let cSum3 := integralCompactSupportOpenSum U V hU hV 3
  let cConn3 := integralCompactSupportOpenConnecting U V hU hV 3
  let hDiff0 := integralOpenUnionHomologyDifference U V 0
  let hSum0 := integralOpenUnionHomologySum U V 0
  let d3Pair := biprod.map d3U d3V
  let : IsIso d3U := hD3U
  let : IsIso d3V := hD3V
  let : IsIso d3I := hD3I
  let : IsIso d3Pair := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · apply (ModuleCat.mono_iff_injective _).mp
      infer_instance
    · apply (ModuleCat.epi_iff_surjective _).mp
      infer_instance
  apply moduleCapD3_union_isIso cDiff3 cSum3 cConn3 hDiff0 hSum0 d3I d3Pair d3Union
  · intro a
    exact congrArg (fun f => f.hom a)
      (integralCompactSupportOpenDifference_sum U V hU hV 3)
  · intro a
    have h := congrArg (fun f => f.hom a)
      (integralCompactSupportCapThree_union_difference_square U V hU hV hDY omegaY hlocalY)
    simpa [d3Pair, d3I, cDiff3, hDiff0] using h.symm
  · intro v
    have h := congrArg (fun f => f.hom v)
      (integralCompactSupportCapThree_union_sum_square U V hU hV hDY omegaY hlocalY)
    simpa [d3Pair, d3U, d3V, cSum3, hSum0] using h
  · intro x hx
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralCompactSupportOpenMayerVietoris_exact_union U V hU hV 3) x hx
    exact ⟨w, hw⟩
  · intro w hw
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralOpenUnionHomologyMayerVietoris_exact U V hU hV 0) w hw
    exact ⟨z, hz⟩
  · exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  · exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  · exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · exact (ModuleCat.epi_iff_surjective _).mp
      (integralOpenUnionHomologySum_zero_epi U V hU hV)
  · exact hC4

end Poincare.Topology
