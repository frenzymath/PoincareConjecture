import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Definitions.M37SurgeryFlow
import PoincareConjecture.Proofs.M52.Volume









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



def m52CoreFlowData
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) :
    RepairedSurgeryFlowData.{u} G.certificate.flow.standard_initial :=
  { flow := G.certificate.flow
    standard_initial_eq := rfl }

theorem m52CoreFlowData_flow
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) :
    (m52CoreFlowData G).flow = G.certificate.flow := rfl


theorem RepairedGlobalFlowData.terminalPolicy
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) :
    SurgeryFlowTerminalPolicyOn G.certificate.flow G.certificate.flow.time_domain := by
  rw [G.flow_eq]
  exact G.schedule.terminal_policy

private theorem noSurgeryAfterEmpty (F : SurgeryFlowData.{u})
    (s : ℝ) (hs : s ∈ F.time_domain) (hempty : IsEmpty (F.slice s).carrier)
    (t : ℝ) (ht : t ∈ F.time_domain) (hst : s < t) : t ∉ F.surgery_times := by
  intro hevent
  let : IsEmpty (F.slice t).carrier := F.extinction_permanent s t hs ht hst.le hempty
  let E := F.vanishing_event t hevent
  let a := max s E.tMinus
  have hat : a < t := max_lt hst E.tMinus_lt
  have hsa : s ≤ a := le_max_left _ _
  have ha : a ∈ F.time_domain := F.time_domain_interval.out hs ht ⟨hsa, hat.le⟩
  let : IsEmpty (F.slice a).carrier := F.extinction_permanent s a hs ha hsa hempty
  obtain ⟨x⟩ := E.pre_nonempty
  exact isEmptyElim (E.pre_identify ⟨a, le_max_right _ _, hat⟩ x)




theorem m52GlobalFlowDataFromSchedule
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)} (G : RepairedGlobalScheduleData N) :
    ∃ R : RepairedGlobalFlowData N, R.schedule = G := by
  let certificate : GlobalSurgeryFlowCertificate N := {
    flow := G.flow
    schedule := G.schedule
    control_function := G.control_function
    control_antitone := G.control_antitone
    control_positive := G.control_positive
    control_eq := G.control_eq
    schedule_standard_initial := G.schedule_standard_initial
    parameters_epsilon_eq := G.parameters_epsilon_eq
    parameters_C_eq := G.parameters_C_eq
    time_domain_eq := G.time_domain_eq
    initial_identification := G.initial_identification
    initial_metric_pullback := G.initial_metric_pullback
    no_two_sided_projective_plane := G.flow.no_two_sided_projective_plane
    local_finite := G.local_finite
    no_finite_accumulation := by
      intro T _hT
      refine ⟨1, by norm_num, ?_⟩
      apply (G.local_finite (Set.Icc (T - 1) (T + 1)) isCompact_Icc).subset
      intro t ht
      exact ⟨ht.1, ht.2.1.le, ht.2.2.le⟩
    canonical := G.canonical
    noncollapsed := G.noncollapsed
    pinched := G.pinched
    admissible := G.admissible
    schedule_agreement := G.schedule_agreement
    volume_bound_on_compacts := m52VolumeBoundOnCompacts G.volume_loss
    volume_loss_on_compacts := m52VolumeLossOnCompacts G.volume_loss
    component_event_count_on_compacts := m52ComponentEventCountOnCompacts G.volume_loss
    volume_growth_on_compacts := m52VolumeGrowthOnCompacts G.volume_loss
    no_surgery_after_empty := noSurgeryAfterEmpty G.flow
    permanent_empty := G.flow.extinction_permanent
  }
  exact ⟨⟨G, certificate, rfl, HEq.rfl, rfl⟩, rfl⟩

end PoincareConjecture
