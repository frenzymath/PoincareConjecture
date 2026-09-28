import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.CalibratedHorns
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.SmallConstant

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}

theorem continuation_of_constant_le_ninetyNine
    (B : RepairedContinuationLimitBridge H L N I) (P : M33Predecessors.{u})
    (hcoreNe : I.controlled_core.Nonempty) (hconstant : H.constant ≤ 99) :
    Nonempty (RepairedBranchContinuationData I) := by
  apply B.continuation_of_calibrated_horns P hcoreNe
  intro K hK e
  have hrho : I.rho < H.r₀ := B.parameter_r₀_eq.symm ▸ I.rho_lt_r₀
  obtain ⟨horn, hcomponent, hlow, htail, hboundary, hlinear⟩ :=
    N.limit.exists_calibrated_strongHorn_of_constant_le_ninetyNine
      B.appendixA B.appendixA_accuracy K e I.rho I.rho_pos hrho B.constant_one_le
      hconstant hK
  refine ⟨horn, hboundary, ?_, hcomponent, ?_, htail⟩
  · intro x hx
    rw [← N.limit.terminal_scalar_eq]
    have hpos : 0 < H.constant * I.rho⁻¹ ^ 2 :=
      mul_pos H.constant_pos (sq_pos_of_pos (inv_pos.mpr I.rho_pos))
    nlinarith [hlinear x hx]
  · simpa only [N.limit.terminal_scalar_eq] using hlow

end PoincareConjecture.RepairedContinuationLimitBridge
