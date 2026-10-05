import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Compatibility
import PoincareLib.Topology.Manifold.Surgery.Event.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Global.Existence
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.LocalTopology

open scoped PoincareMT.BoundedDistanceSource
local macro "rawLocalSurgeryTopology.topology" : term =>
  `(PoincareMT.M38.exists_raw_local_surgery_topology_data)
/-!
# Calibrated raw-flow topology provider for M72

Choose the Proposition 15.3 epsilon threshold before the global schedule.
The M52 normalized-flow branch retains the same bound, so the raw M38
theorem applies to its exact flow and admissibility certificate. This is
predecessor assembly, with no reconstruction or endpoint assumption.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem m72GlobalEpsilonBound
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) {K : MetricSurgeryConstants}
    (schedule : GlobalSurgerySchedule K)
    (hK : G.schedule.flow.local_constants = K)
    (hschedule : HEq G.schedule.schedule schedule)
    {bound : ℝ} (hbound : 2 * schedule.setup.epsilon ≤ bound) :
    2 * G.certificate.flow.parameters.epsilon ≤ bound := by
  rw [G.flow_eq, G.schedule.parameters_epsilon_eq]
  cases hK
  have hs : G.schedule.schedule = schedule := eq_of_heq hschedule
  rw [hs]
  exact hbound

/-
Natural-language theorem: given the neck/cap and global-flow predecessor
services, choose one surgery schedule before the initial manifold and control
function. Every nonempty compact normalized initial manifold with no embedded
projective plane of trivial normal bundle, and every positive non-increasing
control function bounded by that schedule, then admits an M52 flow together
with the raw M38 local topology data for that same flow. The proof chooses
M38's universal epsilon threshold first and passes it to M52.

Source: Morgan--Tian Proposition 15.3, pp. 357--358, the epsilon selection
in Section 15.1.1, pp. 354--355, and Theorem 15.9, pp. 363--364. This checked
adapter adds no mathematical admission.
-/
theorem m72GlobalFlowWithRawTopology
    (A : RepairedNeckCapTopologyTheory.{u})
    (B28 : RepairedBoundedDistanceTheory.{u})
    (E34 : RepairedStandardCapExistenceTheory)
    (U35 : RepairedStandardCapUniquenessTheory)
    (S36 : RepairedMetricSurgeryTheory.{u})
    (P44 : RepairedCapPersistenceTheory.{u})
    (L15 : GeneralizedNoncollapsingConclusion.{u} 3)
    (U43 : RepairedUnifiedContinuationTheory.{u})
    (S45 : RepairedControlledSchedulesTheory.{u})
    (N46 : RepairedNoncollapseInductionTheory.{u})
    (C47 : RepairedCanonicalInductionTheory.{u})
    (E48 : RepairedEpochExtensionTheory.{u})
    (P48 : M48Predecessors.{u})
    (V49 : RepairedVolumeLossTheory.{u})
    (F50 : RepairedFinitePrefixTheory.{u})
    (G51 : RepairedGlobalScheduleTheory.{u}) :
    ∃ K : MetricSurgeryConstants, ∃ schedule : GlobalSurgerySchedule K,
      ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [CompactSpace M] [Nonempty M],
        ∀ (N : NormalizedInitialMetric (M := M)),
          NoTrivialNormalProjectivePlane (M := M) →
          ∀ delta : ℝ → ℝ,
            AntitoneOn delta (Set.Ici 0) →
            (∀ t, 0 ≤ t → 0 < delta t) →
            (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t → delta t ≤ schedule.Delta j) →
            ∃ G : RepairedGlobalFlowData N,
              G.schedule.flow.local_constants = K ∧
              HEq G.schedule.schedule schedule ∧
              G.schedule.control_function = delta ∧
              Nonempty (RawLocalSurgeryTopologyData G.certificate.flow) := by
  obtain ⟨epsilon, hepsilon, _hneck, htopology⟩ := rawLocalSurgeryTopology.topology A
  obtain ⟨K, schedule, hbound, _extend, start⟩ :=
    repairedGlobalFlow.global_flow B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49
      F50 G51 epsilon hepsilon
  refine ⟨K, schedule, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ N hprojective delta hantitone hpositive hcutoff
  obtain ⟨G, hK, hschedule, hdelta⟩ :=
    start N hprojective delta hantitone hpositive hcutoff
  exact ⟨G, hK, hschedule, hdelta,
    htopology G.certificate.flow G.certificate.admissible
      (m72GlobalEpsilonBound G schedule hK hschedule hbound)⟩

/-- Assemble M72's input on the exact global flow once M71 supplies extinction.
M38 supplies local topology and M52 supplies finite event chronology; no
separate terminal-event identification or global reconstruction is assumed. -/
noncomputable def m72ReconstructionInputFromRaw
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (E : FiniteExtinctionConclusion G.certificate.flow)
    (hconnected : IsConnected (Set.univ : Set M)) : M72ReconstructionInput N where
  global := G
  extinction := E
  initial_connected := hconnected
  local_topology := m72LocalTopologyFromRaw G.certificate L E.extinction_time

end PoincareMT
