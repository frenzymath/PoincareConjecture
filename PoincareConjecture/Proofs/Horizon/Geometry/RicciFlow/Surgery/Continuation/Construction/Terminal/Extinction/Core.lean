import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B

theorem core_nonempty_iff_terminal_sublevel :
    I.controlled_core.Nonempty ↔ ∃ z, N.limit.terminal_scalar z ≤ I.rho⁻¹ ^ 2 := by
  rw [B.core_status_iff]
  constructor
  · rintro ⟨_, _, z, _, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨N.limit.terminal_source z,
      N.limit.terminal_source_image ▸ mem_range_self z, z, rfl, hz⟩

theorem core_empty_iff_terminal_sublevel_empty :
    I.controlled_core = ∅ ↔ {z | N.limit.terminal_scalar z ≤ I.rho⁻¹ ^ 2} = ∅ := by
  rw [← not_nonempty_iff_eq_empty, ← not_nonempty_iff_eq_empty]
  exact not_congr B.core_nonempty_iff_terminal_sublevel

theorem terminal_scalar_gt_of_core_empty (hempty : I.controlled_core = ∅)
    (z : (N.limit.extension.extended.slice T).carrier) :
    I.rho⁻¹ ^ 2 < N.limit.terminal_scalar z := by
  apply lt_of_not_ge
  intro hz
  have hne := B.core_nonempty_iff_terminal_sublevel.mpr ⟨z, hz⟩
  simp only [hempty, Set.not_nonempty_empty] at hne

theorem terminal_components_eq_empty_of_core_empty (hempty : I.controlled_core = ∅) :
    SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T)
      (F.parameters.delta T * F.parameters.r T) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨y, hy, _⟩
  have hlt := B.terminal_scalar_gt_of_core_empty hempty y
  rw [N.limit.terminal_scalar_eq, I.rho_eq] at hlt
  exact hlt.not_ge hy

end PoincareConjecture.RepairedContinuationLimitBridge
