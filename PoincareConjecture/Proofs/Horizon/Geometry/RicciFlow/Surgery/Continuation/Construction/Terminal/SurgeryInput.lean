import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Pinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace RepairedContinuationInput

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)

include I

theorem terminal_delta_lt_half : F.parameters.delta T < 1 / 2 := by
  have h := I.terminal_delta_bound.trans_lt F.local_constants.delta₀_lt
  linarith

theorem terminal_height_scalar_large :
    F.local_constants.R₀ ≤ (F.parameters.h T)⁻¹ ^ 2 := by
  have hh := F.parameters.h_pos T I.terminal_pos.le
  have hsquare : (F.parameters.h T) ^ 2 ≤ F.local_constants.R₀⁻¹ := by
    calc
      (F.parameters.h T) ^ 2 ≤
          (F.local_constants.R₀ ^ (-1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hh.le I.terminal_height_bound 2
      _ = F.local_constants.R₀⁻¹ := by
        rw [← Real.rpow_mul_natCast F.local_constants.R₀_pos.le]
        norm_num [Real.rpow_neg_one]
  simpa only [inv_pow] using
    (le_inv_comm₀ (sq_pos_of_pos hh) F.local_constants.R₀_pos).mp hsquare

def terminalSurgeryInput {G : GeneralizedRicciFlowData.{u}}
    (E : GeneralizedFlowExtension G T)
    (N : TerminalStrongNeck E (F.parameters.delta T))
    (hscalar : (E.extended.connection T).scalarCurvature N.center =
      (F.parameters.h T)⁻¹ ^ 2)
    (hpinched : SurgeryPinchedAt (E.extended.connection T) T) :
    MetricSurgeryInput F.local_constants (E.extended.metric T) where
  neck := N.spatialNeck I.terminal_delta_lt_half
  time := T
  delta_le := I.terminal_delta_bound
  scalar_large := hscalar.symm ▸ I.terminal_height_scalar_large
  pinched := ⟨hpinched.1, fun x _ => hpinched.2.1 x (Set.mem_univ x),
    fun x _ => hpinched.2.2 x (Set.mem_univ x)⟩

end RepairedContinuationInput

namespace RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {I : RepairedContinuationInput F T}

theorem exists_terminal_surgery
    (bridge : RepairedContinuationLimitBridge H L N I)
    (horn : StrongHorn N.limit.extension (terminalAccuracyFactor * H.epsilon))
    (hboundary : HornBoundaryBelow horn (I.rho / (2 * H.constant))) :
    ∃ neck : TerminalStrongNeck N.limit.extension (F.parameters.delta T),
      neck.center ∈ horn.carrier ∧ neck.carrier ⊆ horn.carrier ∧
      (N.limit.extension.extended.connection T).scalarCurvature neck.center =
        (F.parameters.h T)⁻¹ ^ 2 ∧
      Nonempty (HornEndCut horn neck I.rho) ∧
      ∃ J : MetricSurgeryInput F.local_constants (N.limit.extension.extended.metric T),
        J.neck = neck.spatialNeck I.terminal_delta_lt_half ∧
        J.time = T ∧ Nonempty (MetricSurgeryResult F.standard_initial J) := by
  obtain ⟨deep⟩ := bridge.deep_horn_application horn hboundary
  obtain ⟨neck, hcenter, hcarrier, hscalar, hcut⟩ := deep.selected_neck
  let J := I.terminalSurgeryInput N.limit.extension neck hscalar
    (Surgery.Terminal.terminal_pinched H N.limit)
  exact ⟨neck, hcenter, hcarrier, hscalar, hcut, J, rfl, rfl,
    bridge.surgery_operation J⟩

end RepairedContinuationLimitBridge

end PoincareConjecture
