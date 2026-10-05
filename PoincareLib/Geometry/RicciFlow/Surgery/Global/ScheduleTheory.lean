import PoincareLib.Geometry.RicciFlow.Surgery.Global.ScheduleData
import PoincareLib.Geometry.RicciFlow.Surgery.Control.ScheduleTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Volume.FinitePrefixTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossTheory
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Theory

/-!
Adapted from Mapher `PoincareMT/Statements/M51GlobalSchedule.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M51 repaired global schedule induction statement

The controlled schedule and finite-prefix induction have two source-facing
outputs: they extend every already given finite controlled flow on `[0,T)` on
that same changing carrier, and they start a partial global flow from every
normalized initial metric and admissible control function. The provider inputs
record the required services. Constructing their compatible applications,
including the continuation bridge and observed analytic controls, is derived
in the reviewed M51 global assembly contract and owned by its single admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-!
Natural-language theorem: there are global surgery parameter sequences such
that every already given finite changing-carrier flow on `[0,T)` satisfying
the Definition 15.8 event policy, source controls and schedule bounds extends
on the same flow to
`[0,∞)`, with the controls and compact-interval surgery finiteness preserved.
Separately, every nonempty normalized compact initial metric with no trivial
normal projective plane admits a partial global schedule. The latter output
carries the actual changing-carrier flow, every exact finite-prefix witness,
the initial metric identification, schedule agreement, and compact-interval
surgery finiteness and whole-domain terminal policy. The extended given flow
also retains this event policy. M48 owns the guarded finite next-epoch
continuation. M51
must apply it to compatible induction data and assemble both source branches;
its output does not assume another universal continuation service. M52
assembles the complete controlled global certificate.
The common schedule is tightened below the selected M49 loss cutoff before
the external control function or flow is chosen. The normalized branch
retains the resulting selected volume certificate on its same raw flow,
together with the event-history predicates required to instantiate that
certificate; these are outputs of the global construction, not inferred from
the weaker admissibility record.
For any prescribed positive epsilon bound, the schedule is chosen with
twice its setup epsilon below that bound. This choice precedes the other
setup parameters and is retained by both output branches.

Source: Morgan--Tian Theorem 15.9 and Corollary 15.10, printed pp. 363--366,
with the inductive schedule construction in Section 15 and the finite-prefix
argument in Section 17.2, pp. 408--411 (arXiv V2 pp. 395--397).  The
finite-horizon volume-loss input inherits the corrected scaling erratum in
`reviews/errata/2026-09-10-surgery-extinction-audit.md`; no new `h^2` claim is
made here. M48 uses the actual M47 component estimate and M45 model estimates
to calibrate its selector before choosing induction data. Its internal M31
analytic radius and coefficient are not identified with the public r and C.
-/
structure RepairedGlobalScheduleTheory : Prop where
  uniform_schedule :
    DenseBoundedDistanceTheory.{u} →
    RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    RepairedCapPersistenceTheory.{u} →
    GeneralizedNoncollapsingConclusion.{u} 3 →
    RepairedUnifiedContinuationTheory.{u} →
    RepairedControlledSchedulesTheory.{u} →
    RepairedNoncollapseInductionTheory.{u} →
    RepairedCanonicalInductionTheory.{u} →
    RepairedEpochExtensionTheory.{u} →
    M48Predecessors.{u} →
    RepairedVolumeLossTheory.{u} →
    RepairedFinitePrefixTheory.{u} →
      ∀ epsilon_bound : ℝ, 0 < epsilon_bound →
        ∃ K : MetricSurgeryConstants,
          ∃ schedule : GlobalSurgerySchedule K,
            2 * schedule.setup.epsilon ≤ epsilon_bound ∧
            (∀ (delta : ℝ → ℝ),
              AntitoneOn delta (Set.Ici 0) →
              (∀ t, 0 ≤ t → 0 < delta t) →
              (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
                delta t ≤ schedule.Delta j) →
              ∀ (F : SurgeryFlowData.{u}) (T : ℝ),
                RepairedGlobalControlledPrefix schedule delta F T →
                  Nonempty (RepairedGlobalControlledExtension schedule F)) ∧
            (∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
              [BorelSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
              [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
              [SecondCountableTopology M] [CompactSpace M] [Nonempty M],
              (N : NormalizedInitialMetric (M := M)) →
              NoTrivialNormalProjectivePlane (M := M) →
              (delta : ℝ → ℝ) →
              AntitoneOn delta (Set.Ici 0) →
              (∀ t, 0 ≤ t → 0 < delta t) →
              (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
                delta t ≤ schedule.Delta j) →
              ∃ G : RepairedGlobalScheduleData N,
                G.flow.local_constants = K ∧
                HEq G.schedule schedule ∧
                G.control_function = delta)

end PoincareMT
