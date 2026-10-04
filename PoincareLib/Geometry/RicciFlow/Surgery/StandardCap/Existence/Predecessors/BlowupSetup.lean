import PoincareLib.Geometry.RicciFlow.AncientKappa.Rescaling.Construction
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem ancientBlowupSequenceSetupTheory (n : ℕ)
    (hM10 : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution n M) (_reference : M),
      AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientBlowupSetupTheory.{u} n := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _ _ _ K reference tau tau_pos tau_tendsto
  exact ancientBlowupSequenceSetup n M K reference tau tau_pos tau_tendsto
    (hM10 M K reference) hM13

end PoincareMT
