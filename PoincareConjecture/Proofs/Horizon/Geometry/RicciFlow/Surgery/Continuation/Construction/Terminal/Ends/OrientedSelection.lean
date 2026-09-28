import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.SurgeryInput
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.HornNonFilling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {I : RepairedContinuationInput F T}

theorem exists_oriented_terminal_cut
    (B : RepairedContinuationLimitBridge H L N I)
    (horn : StrongHorn N.limit.extension (terminalAccuracyFactor * H.epsilon))
    (hboundary : HornBoundaryBelow horn (I.rho / (2 * H.constant))) :
    ∃ neck : TerminalStrongNeck N.limit.extension (F.parameters.delta T),
      neck.center ∈ horn.carrier ∧ neck.carrier ⊆ horn.carrier ∧
      (N.limit.extension.extended.connection T).scalarCurvature neck.center =
        (F.parameters.h T)⁻¹ ^ 2 ∧
      ∃ cut : HornEndCut horn neck I.rho,
        ∃ D : SurgeryEndCut (neck.spatialNeck I.terminal_delta_lt_half),
          D.tail = cut.carrier := by
  obtain ⟨deep⟩ := B.deep_horn_application horn hboundary
  obtain ⟨neck, hcenter, hcarrier, hscalar, ⟨cut⟩⟩ := deep.selected_neck
  have hδ : F.parameters.delta T ≤ 1 / 200 :=
    (I.terminal_delta_bound.trans_lt F.local_constants.delta₀_lt).le
  have hε : 0 < terminalAccuracyFactor * H.epsilon :=
    mul_pos terminalAccuracyFactor_pos H.epsilon_pos
  rcases cut.exists_oriented_surgeryEndCut B.appendixA hε B.appendixA_accuracy hδ hcarrier
      with ⟨D, hD⟩ | ⟨D, hD⟩
  · exact ⟨neck, hcenter, hcarrier, hscalar, cut, D, hD⟩
  · exact ⟨neck.reversed, hcenter, hcarrier, hscalar, cut.reversed, D, hD⟩

end PoincareConjecture.RepairedContinuationLimitBridge
