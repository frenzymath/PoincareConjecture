import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralOpenOrientation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralOpenHomeomorphData
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenMV

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

universe u

namespace Poincare.Topology

theorem integralOpenSupportDetectedData
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (U : Set Y) (hDY : ∀ L : Set Y, IsCompact L →
    _root_.Poincare.Topology.IntegralSupportDetected L 3) (hU : IsOpen U) :
    ∀ L : Set U, IsCompact L → _root_.Poincare.Topology.IntegralSupportDetected L 3 :=
  _root_.Poincare.Topology.integralSupportDetected_of_openEmbedding hDY
    (_root_.Poincare.Topology.integralOpenSubtypeVal U)
    (_root_.Poincare.Topology.integralOpenSubtypeVal_isOpenEmbedding U hU)

def integralOpenOmegaData
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {U : Set Y}
    [LocallyCompactSpace U] (hU : IsOpen U)
    (omegaY : ∀ y : Y,
      _root_.Poincare.Topology.integralSupportHomology ({y} : Set Y) 3) :
    ∀ x : U, _root_.Poincare.Topology.integralSupportHomology ({x} : Set U) 3 :=
  _root_.Poincare.Topology.integralOpenOrientation
    (_root_.Poincare.Topology.integralOpenSubtypeVal U)
    (_root_.Poincare.Topology.integralOpenSubtypeVal_isOpenEmbedding U hU) omegaY

theorem integralOpenLocalOrientationData
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {U : Set Y}
    [LocallyCompactSpace U] (hU : IsOpen U)
    (omegaY : ∀ y : Y,
      _root_.Poincare.Topology.integralSupportHomology ({y} : Set Y) 3)
    (hlocalY : ∀ y : Y, ∃ B : Set Y, IsOpen B ∧ y ∈ B ∧
      ∃ c : _root_.Poincare.Topology.integralSupportHomology B 3,
        ∀ z : Y, ∀ hz : z ∈ B,
        _root_.Poincare.Topology.integralSupportHomologyRestriction
          (singleton_subset_iff.mpr hz) 3 c = omegaY z) :
    ∀ x : U, ∃ W : Set U, IsOpen W ∧ x ∈ W ∧
      ∃ c : _root_.Poincare.Topology.integralSupportHomology W 3,
        ∀ z : U, ∀ hz : z ∈ W,
        _root_.Poincare.Topology.integralSupportHomologyRestriction
          (singleton_subset_iff.mpr hz) 3 c =
          integralOpenOmegaData hU omegaY z :=
  _root_.Poincare.Topology.integralOpenOrientation_locallyRepresented
    (_root_.Poincare.Topology.integralOpenSubtypeVal U)
    (_root_.Poincare.Topology.integralOpenSubtypeVal_isOpenEmbedding U hU)
    omegaY hlocalY

end Poincare.Topology
