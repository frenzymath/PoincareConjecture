import PoincareConjecture.Proofs.M02.Topology.IntegralCapUnionInduction
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMVIntersection
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenUnionMayerVietoris
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCap
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMV

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]

theorem integralCompactSupportCapOne_union_epi_of_squares
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : ∀ L : Set U, IsCompact L → IntegralSupportDetected L 3)
    (hDV : ∀ L : Set V, IsCompact L → IntegralSupportDetected L 3)
    (hDI : ∀ L : Set ↥(U ∩ V), IsCompact L → IntegralSupportDetected L 3)
    (hDUnion : ∀ L : Set ↥(U ∪ V), IsCompact L → IntegralSupportDetected L 3)
    (omegaU : ∀ x : U, integralSupportHomology ({x} : Set U) 3)
    (omegaV : ∀ x : V, integralSupportHomology ({x} : Set V) 3)
    (omegaI : ∀ x : ↥(U ∩ V), integralSupportHomology ({x} : Set ↥(U ∩ V)) 3)
    (omegaUnion : ∀ x : ↥(U ∪ V), integralSupportHomology ({x} : Set ↥(U ∪ V)) 3)
    (hlocalU : ∀ x : U, ∃ W : Set U, IsOpen W ∧ x ∈ W ∧
      ∃ c : integralSupportHomology W 3, ∀ y : U, ∀ hy : y ∈ W,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaU y)
    (hlocalV : ∀ x : V, ∃ W : Set V, IsOpen W ∧ x ∈ W ∧
      ∃ c : integralSupportHomology W 3, ∀ y : V, ∀ hy : y ∈ W,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaV y)
    (hlocalI : ∀ x : ↥(U ∩ V), ∃ W : Set ↥(U ∩ V), IsOpen W ∧ x ∈ W ∧
      ∃ c : integralSupportHomology W 3, ∀ y : ↥(U ∩ V), ∀ hy : y ∈ W,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaI y)
    (hlocalUnion : ∀ x : ↥(U ∪ V), ∃ W : Set ↥(U ∪ V), IsOpen W ∧ x ∈ W ∧
      ∃ c : integralSupportHomology W 3, ∀ y : ↥(U ∪ V), ∀ hy : y ∈ W,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaUnion y)
    (hD1U : Epi (integralCompactSupportCapOne hDU omegaU hlocalU))
    (hD1V : Epi (integralCompactSupportCapOne hDV omegaV hlocalV))
    (hD2U : IsIso (integralCompactSupportCapTwo hDU omegaU hlocalU))
    (hD2V : IsIso (integralCompactSupportCapTwo hDV omegaV hlocalV))
    (hD2I : IsIso (integralCompactSupportCapTwo hDI omegaI hlocalI))
    (hSqDelta :
      integralCompactSupportCapOne hDUnion omegaUnion hlocalUnion ≫
          integralOpenUnionHomologyConnectingToIntersection U V hU hV 1 =
        integralCompactSupportOpenConnecting U V hU hV 1 ≫
          integralCompactSupportCapTwo hDI omegaI hlocalI)
    (hSqDiff :
      integralCompactSupportCapTwo hDI omegaI hlocalI ≫
          integralOpenUnionHomologyDifference U V 1 =
        integralCompactSupportOpenDifference U V hU hV 2 ≫
          biprod.map (integralCompactSupportCapTwo hDU omegaU hlocalU)
            (integralCompactSupportCapTwo hDV omegaV hlocalV))
    (hSqSum :
      integralCompactSupportOpenSum U V hU hV 1 ≫
          integralCompactSupportCapOne hDUnion omegaUnion hlocalUnion =
        biprod.map (integralCompactSupportCapOne hDU omegaU hlocalU)
            (integralCompactSupportCapOne hDV omegaV hlocalV) ≫
          integralOpenUnionHomologySum U V 2)
    (hHsum : ∀ y, integralOpenUnionHomologyConnectingToIntersection U V hU hV 1 y = 0 →
      ∃ w, (integralOpenUnionHomologySum U V 2).hom w = y) :
    Epi (integralCompactSupportCapOne hDUnion omegaUnion hlocalUnion) := by
  let cDelta := integralCompactSupportOpenConnecting U V hU hV 1
  let cDiff := integralCompactSupportOpenDifference U V hU hV 2
  let cSum := integralCompactSupportOpenSum U V hU hV 1
  let hDelta := integralOpenUnionHomologyConnectingToIntersection U V hU hV 1
  let hDiff := integralOpenUnionHomologyDifference U V 1
  let hSum := integralOpenUnionHomologySum U V 2
  let d1U := integralCompactSupportCapOne hDU omegaU hlocalU
  let d1V := integralCompactSupportCapOne hDV omegaV hlocalV
  let d2U := integralCompactSupportCapTwo hDU omegaU hlocalU
  let d2V := integralCompactSupportCapTwo hDV omegaV hlocalV
  let d2I := integralCompactSupportCapTwo hDI omegaI hlocalI
  let dUnion := integralCompactSupportCapOne hDUnion omegaUnion hlocalUnion
  have hExactC : ∀ z, cDiff z = 0 → ∃ x, cDelta x = z := by
    intro z hz
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (integralCompactSupportOpenMayerVietoris_exact_intersection U V hU hV 1) z hz
    exact ⟨x, hx⟩
  have hExactH : ∀ y, hDelta y = 0 → ∃ w, hSum.hom w = y := by
    intro y hy
    exact hHsum y hy
  let : Epi d1U := hD1U
  let : Epi d1V := hD1V
  let : IsIso d2U := hD2U
  let : IsIso d2V := hD2V
  let : IsIso d2I := hD2I
  have hD2pair : Function.Injective (biprod.map d2U d2V) := by
    apply (ModuleCat.mono_iff_injective _).mp
    infer_instance
  have hD2Isurj : Function.Surjective d2I := by
    apply (ModuleCat.epi_iff_surjective _).mp
    infer_instance
  have hD1Usurj : Function.Surjective d1U :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hD1Vsurj : Function.Surjective d1V :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  apply (ModuleCat.epi_iff_surjective _).mpr
  apply moduleCapD1_union_surjective cDelta cDiff cSum hDelta hDiff hSum
    d1U d1V d2U d2V d2I dUnion
  · exact hSqDelta
  · exact hSqDiff
  · exact hSqSum
  · exact (integralOpenUnionHomologyConnecting_difference U V hU hV 1)
  · exact hExactC
  · exact hExactH
  · exact hD2pair
  · exact hD2Isurj
  · exact hD1Usurj
  · exact hD1Vsurj

end PoincareConjecture.Proofs.M02.Topology
