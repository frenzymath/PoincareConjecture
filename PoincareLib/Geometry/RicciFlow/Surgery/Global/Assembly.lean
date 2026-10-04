import PoincareLib.Geometry.RicciFlow.Surgery.Global.SelectedCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.CompatibilityData
import PoincareLib.Geometry.RicciFlow.Surgery.Volume.CompactBounds

/-!
Adapted from Mapher `PoincareMT/Proofs/M52/Assembly.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# The M52 certificate on the exact M51 flow

The geometric controls are M51 outputs; the four volume fields are checked
applications of its selected raw M49 certificate. No operation alignment,
new flow, or additional analytic admission is introduced here.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The raw flow boundary needed by M39--M71 is obtained directly from the
    global certificate.  It carries no optional M36 operation provenance. -/
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

/-- The M51 event policy applies to the exact flow in the M52 certificate. -/
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

/-- Assemble the global certificate from M51's actual schedule/flow and the
selected M49 volume output. This is a logical consequence of the preceding
contracts for Theorem 15.9, not another analytic version of that theorem. -/
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

end PoincareMT
