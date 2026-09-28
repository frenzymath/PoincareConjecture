import PoincareConjecture.Proofs.M02.Topology.IntegralOpenOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenHomeomorphData
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMV



set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02

theorem integralOpenSupportDetectedData
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (U : Set Y) (hDY : ∀ L : Set Y, IsCompact L →
    _root_.PoincareConjecture.Proofs.M02.Topology.IntegralSupportDetected L 3) (hU : IsOpen U) :
    ∀ L : Set U, IsCompact L → _root_.PoincareConjecture.Proofs.M02.Topology.IntegralSupportDetected L 3 :=
  _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportDetected_of_openEmbedding hDY
    (_root_.PoincareConjecture.Proofs.M02.Topology.integralOpenSubtypeVal U)
    (_root_.PoincareConjecture.Proofs.M02.Topology.integralOpenSubtypeVal_isOpenEmbedding U hU)

def integralOpenOmegaData
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {U : Set Y}
    [LocallyCompactSpace U] (hU : IsOpen U)
    (omegaY : ∀ y : Y,
      _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomology ({y} : Set Y) 3) :
    ∀ x : U, _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomology ({x} : Set U) 3 :=
  _root_.PoincareConjecture.Proofs.M02.Topology.integralOpenOrientation
    (_root_.PoincareConjecture.Proofs.M02.Topology.integralOpenSubtypeVal U)
    (_root_.PoincareConjecture.Proofs.M02.Topology.integralOpenSubtypeVal_isOpenEmbedding U hU) omegaY

theorem integralOpenLocalOrientationData
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {U : Set Y}
    [LocallyCompactSpace U] (hU : IsOpen U)
    (omegaY : ∀ y : Y,
      _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomology B 3,
        ∀ z : Y, ∀ hz : z ∈ B,
        _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomologyRestriction
          (singleton_subset_iff.mpr hz) 3 c = omegaY z) :
    ∀ x : U, ∃ W : Set U, IsOpen W ∧ x ∈ W ∧
      ∃ c : _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomology W 3,
        ∀ z : U, ∀ hz : z ∈ W,
        _root_.PoincareConjecture.Proofs.M02.Topology.integralSupportHomologyRestriction
          (singleton_subset_iff.mpr hz) 3 c =
          integralOpenOmegaData hU omegaY z :=
  _root_.PoincareConjecture.Proofs.M02.Topology.integralOpenOrientation_locallyRepresented
    (_root_.PoincareConjecture.Proofs.M02.Topology.integralOpenSubtypeVal U)
    (_root_.PoincareConjecture.Proofs.M02.Topology.integralOpenSubtypeVal_isOpenEmbedding U hU)
    omegaY hlocalY

end PoincareConjecture.Proofs.M02
