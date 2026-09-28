import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapGlobalInduction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapSquares
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapDifferenceSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCapSumSquare
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenUnionMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenCapData


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology


variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]
  [LocallyCompactSpace Y]

theorem integralCompactSupportCapOne_union_epi_canonical
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    [LocallyCompactSpace U] [LocallyCompactSpace V]
    [LocallyCompactSpace ↥(U ∩ V)] [LocallyCompactSpace ↥(U ∪ V)]
    (hDY : ∀ L : Set Y, IsCompact L → IntegralSupportDetected L 3)
    (omegaY : ∀ y : Y, integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ z : Y, ∀ hz : z ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) 3 c = omegaY z)
    (hD1U : Epi (integralCompactSupportCapOne
      (integralOpenSupportDetectedData U hDY hU)
      (integralOpenOmegaData hU omegaY)
      (integralOpenLocalOrientationData hU omegaY hlocalY)))
    (hD1V : Epi (integralCompactSupportCapOne
      (integralOpenSupportDetectedData V hDY hV)
      (integralOpenOmegaData hV omegaY)
      (integralOpenLocalOrientationData hV omegaY hlocalY)))
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
      (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY))) :
    Epi (integralCompactSupportCapOne
      (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
      (integralOpenOmegaData (hU.union hV) omegaY)
      (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)) := by
  apply integralCompactSupportCapOne_union_epi_of_squares U V hU hV
    (integralOpenSupportDetectedData U hDY hU)
    (integralOpenSupportDetectedData V hDY hV)
    (integralOpenSupportDetectedData (U ∩ V) hDY (hU.inter hV))
    (integralOpenSupportDetectedData (U ∪ V) hDY (hU.union hV))
    (integralOpenOmegaData hU omegaY)
    (integralOpenOmegaData hV omegaY)
    (integralOpenOmegaData (hU.inter hV) omegaY)
    (integralOpenOmegaData (hU.union hV) omegaY)
    (integralOpenLocalOrientationData hU omegaY hlocalY)
    (integralOpenLocalOrientationData hV omegaY hlocalY)
    (integralOpenLocalOrientationData (hU.inter hV) omegaY hlocalY)
    (integralOpenLocalOrientationData (hU.union hV) omegaY hlocalY)
    hD1U hD1V hD2U hD2V hD2I
    (integralCompactSupportCapOne_union_connecting_square U V hU hV hDY omegaY hlocalY)
    (integralCompactSupportCapTwo_union_difference_square U V hU hV hDY omegaY hlocalY)
    (integralCompactSupportCapOne_union_sum_square U V hU hV hDY omegaY hlocalY)
    ?_
  intro y hy
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (integralOpenUnionHomologyMayerVietoris_exact_union U V hU hV 1) y hy
  exact ⟨w, hw⟩

end Poincare.Topology
