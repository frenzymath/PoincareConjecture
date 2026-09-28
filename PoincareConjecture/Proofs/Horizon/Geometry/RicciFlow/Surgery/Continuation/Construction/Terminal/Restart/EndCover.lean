import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Conclusion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.Policy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Core

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

open Surgery.Terminal.Gluing

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B in
theorem continuation_of_finite_end_cover (P : M33Predecessors.{u})
    {ι : Type u} [Fintype ι]
    (J : ι → MetricSurgeryInput F.local_constants (N.limit.extension.extended.metric T))
    (R : ∀ i, MetricSurgeryResult F.standard_initial (J i))
    (cuts : ∀ i, SurgeryEndCut (J i).neck)
    (hneck : Pairwise (fun i j => Disjoint (J i).neck.carrier (J j).neck.carrier))
    (htails : Pairwise (fun i j => Disjoint (cuts i).tail (cuts j).tail))
    (hcenter : ∀ i, (J i).neck.center ∈
      SurgeryTerminalCoreComponents (N.limit.extension.extended.connection T) I.rho)
    (hcutslow : ∀ i, Disjoint (cuts i).tail
      {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2})
    (hspherelow : ∀ i, Disjoint (J i).neck.central_sphere
      {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2})
    (hcover : ∀ K : TerminalComponentPath N.limit.extension,
      (K.component ∩ {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (cuts i).tail)
    (htime : ∀ i, (J i).time = T)
    (hdelta : ∀ i, (J i).neck.epsilon = F.parameters.delta T)
    (hscale : ∀ i, (J i).neck.scale = F.parameters.h T)
    (hcoreNe : I.controlled_core.Nonempty)
    (ν : ι → TerminalStrongNeck N.limit.extension (F.parameters.delta T))
    (hJneck : ∀ i, (J i).neck = (ν i).spatialNeck
      ((hdelta i) ▸ (J i).neck.epsilon_lt_half)) :
    Nonempty (RepairedBranchContinuationData I) := by
  let D := N.limit.extension.extended.connection T
  let U := policyRetainedOpen D I.rho J cuts
  have hcore : {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} ⊆ U := by
    have hcuts : ∀ i, Disjoint (cuts i).tail {x | D.scalarCurvature x ≤ I.rho⁻¹ ^ 2} := by
      simpa only [N.limit.terminal_scalar_eq] using hcutslow
    have hspheres : ∀ i, Disjoint (J i).neck.central_sphere
        {x | D.scalarCurvature x ≤ I.rho⁻¹ ^ 2} := by
      simpa only [N.limit.terminal_scalar_eq] using hspherelow
    simpa only [N.limit.terminal_scalar_eq] using
      low_subset_policyRetainedOpen D I.rho J cuts hcuts hspheres
  have hU : Nonempty U := by
    obtain ⟨x, hx⟩ := B.core_nonempty_iff_terminal_sublevel.mp hcoreNe
    exact ⟨⟨x, hcore hx⟩⟩
  have hd : Pairwise (fun i j => Disjoint
      ((J i).negativeHalf : Set (N.limit.extension.extended.slice T).carrier)
      (J j).negativeHalf) := by
    intro i j hij
    exact (hneck hij).mono (fun _ hx => hx.1) (fun _ hx => hx.1)
  let σ := I.lateReferenceTime H.reference.tMinus H.reference.tMinus_lt
  exact B.continuation_of_finite_cuts P σ
    (I.lateReferenceTime_close H.reference.tMinus H.reference.tMinus_lt)
    J R U hU hd (policyRetainedOpen_disjoint_central D I.rho J cuts) hneck
    (policyRetainedOpen_neck_inter D I.rho J cuts hneck htails hcenter)
    (frontier_policyRetainedOpen_subset D I.rho J cuts)
    (N.limit.isCompact_closure_policyRetainedOpen I.rho J cuts hcover)
    hcore htime hdelta hscale cuts
    (closure_policyRetainedOpen D I.rho J cuts hneck htails hcenter R)
    hcoreNe ν hJneck

end PoincareConjecture.RepairedContinuationLimitBridge
