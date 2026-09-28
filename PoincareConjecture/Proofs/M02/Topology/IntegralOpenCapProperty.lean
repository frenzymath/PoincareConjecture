import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCap
import PoincareConjecture.Proofs.M02.IntegralOpenCapData

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

variable {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]
  [LocallyCompactSpace X]

def integralOpenCapProperty
    (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocalX : ∀ x : X, ∃ B : Set X, IsOpen B ∧ x ∈ B ∧
      ∃ c : integralSupportHomology B 3, ∀ y : X, ∀ hy : y ∈ B,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)
    (U : Set X) (hU : IsOpen U) : Prop :=
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  Epi (integralCompactSupportCapOne
    (integralOpenSupportDetectedData U hDX hU)
    (integralOpenOmegaData hU omegaX)
    (integralOpenLocalOrientationData hU omegaX hlocalX)) ∧
  IsIso (integralCompactSupportCapTwo
    (integralOpenSupportDetectedData U hDX hU)
    (integralOpenOmegaData hU omegaX)
    (integralOpenLocalOrientationData hU omegaX hlocalX)) ∧
  IsIso (integralCompactSupportCapThree
    (integralOpenSupportDetectedData U hDX hU)
    (integralOpenOmegaData hU omegaX)
    (integralOpenLocalOrientationData hU omegaX hlocalX)) ∧
  ∀ q : Nat, 4 ≤ q → IsZero (integralCompactSupportCohomology U q)

end PoincareConjecture.Proofs.M02.Topology
