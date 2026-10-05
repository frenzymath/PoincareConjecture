import PoincareLib.Geometry.RicciFlow.Surgery.Global.SelectedCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.UnifiedTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Global.ScheduleTheory

/-!
Adapted from Mapher `PoincareMT/Statements/M52GlobalFlow.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M52 repaired global controlled-flow statement

The checked M52 adapter assembles the global certificate on M51's exact flow.
The selected M49 certificate supplies all four volume fields. M51 owns the
global construction. Its source controls do not include
the former unsupported derivative estimate at the geometric constant C.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-!
Natural-language theorem: the M43 continuation provider, controlled schedule
and epoch packages, finite-prefix package, and M51 global schedule provider
determine one surgery-constant package and one global schedule. For every
already given finite controlled flow on `[0,T)` satisfying that same schedule
and the Definition 15.8 terminal event policy,
the output includes an extension of that actual flow to `[0,∞)` with the
source controls preserved. For every
nonempty compact normalized initial metric with no
trivial normal projective plane, and every positive non-increasing control
function bounded on the schedule's half-open epochs, they yield one complete
changing-carrier surgery-flow certificate.  The returned data retains the M51
partial
schedule, identifies its actual flow and schedule with the certificate,
identifies the selected control function, and therefore exposes the
certificate's canonical, noncollapsing, pinching, admissibility, compact
volume, left-limit surgery-loss, local-finiteness, and permanent-empty
properties.  No
fixed-carrier flow or endpoint classification is added.  The source-scale
property uses `h(delta * r, delta)` as in Definition 15.5.
The caller may prescribe any positive bound on doubled setup epsilon; the
selected schedule retains this bound before either flow branch is applied.
The retained M51 schedule also supplies terminal event policy on the exact
certificate flow through the checked
`RepairedGlobalFlowData.terminalPolicy` adapter.

M48 owns guarded finite-epoch extension, M50 supplies finite event bounds,
and M51 owns their compatible global assembly. M52 is a checked logical
adapter: its full certificate uses the same M51 flow and selected M49 volume
data. It introduces no separate analytic claim or admission.

Source: Morgan--Tian Theorem 15.9 and Corollary 15.10, printed pp. 363--366,
with the global changing-carrier and extinction conventions in Sections 15.4
and 17.2, pp. 356--366 and 408--411 (arXiv V2 lines 16813--16849 and
18857--18957).  The corrected surgery-volume scaling recorded in
`reviews/errata/2026-09-10-surgery-extinction-audit.md` is inherited through
M49; this statement makes no independent scaling claim.
-/
structure RepairedGlobalFlowTheory : Prop where
  global_flow :
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
    RepairedGlobalScheduleTheory.{u} →
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
            ∀ (N : NormalizedInitialMetric (M := M)),
              NoTrivialNormalProjectivePlane (M := M) →
              ∀ (delta : ℝ → ℝ),
                AntitoneOn delta (Set.Ici 0) →
                (∀ t, 0 ≤ t → 0 < delta t) →
                (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
                  delta t ≤ schedule.Delta j) →
                ∃ G : RepairedGlobalFlowData N,
                  G.schedule.flow.local_constants = K ∧
                  HEq G.schedule.schedule schedule ∧
                  G.schedule.control_function = delta)

end PoincareMT
