import PoincareLib.Geometry.RicciFlow.Surgery.Global.SelectedCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Path
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Contradiction.Data
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Path.InitialClass
import PoincareLib.Topology.Manifold.ConnectedSum.Reconstruction.Extinction

/-!
# M71 fixed-initial-class extinction boundary

The current M67 interface starts at zero. This conditional Poincare-branch
application fixes one actual initial component, metric, and nonzero class before
choosing any
target time. Paths are normalized to that same initial component and cover
the surviving target slice. M67 supplies class coherence; checked M69 adapters
construct the ledger and the full [0,T] comparison input.

The declared endpoints are simply connected, so Proposition 18.9 is used here
with T1 = 0. The general finite-pi1 late-start and W2 route is an out-of-scope
auxiliary, not an unfilled M71 premise.

Source: Morgan--Tian Theorem 18.1, Proposition 18.9 and Claims 18.19-18.20,
printed pp. 415, 421-422 and 431-432; see the source-alignment contract in
`reviews/contracts/2026-09-16-m71-fixed-class-round1.md` and the first-empty correction in
`reviews/errata/2026-09-16-m71-first-empty-policy.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Actual comparison data for the literal M56 path to a terminal point.
M56 supplies the same selected initial component, including its basepoint,
for every such path. -/
structure M71ComponentContinuationData
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    (ancestry : RepairedFiniteAncestryData D.flow W)
    (B : M59HigherBasepointTransportService)
    (T : ℝ) (hT : T ∈ D.flow.time_domain) where
  terminal_point : (D.flow.slice T).carrier
  K : RepairedComparisonMapData D
  C : RepairedComparisonHomotopyData D K
  H : RepairedAncestryTransportInput D W
      (ancestry.path_for T hT terminal_point) K C
  A : RepairedAncestryTransportData D W
      (ancestry.path_for T hT terminal_point) K C H B

/-- The path in a continuation package is the literal ancestry path selected
    for its terminal point; no re-based path is admitted at this boundary. -/
abbrev M71ComponentContinuationData.P
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {ancestry : RepairedFiniteAncestryData D.flow W}
    {B : M59HigherBasepointTransportService}
    {T : ℝ} {hT : T ∈ D.flow.time_domain}
    (J : M71ComponentContinuationData D W ancestry B T hT) :
    RepairedComponentPath D.flow T W :=
  ancestry.path_for T hT J.terminal_point

/-- Fixed starting data and finite ancestry for every surviving target slice.
The sole initial class and strict event bounds occur before the target-time
quantifier. Components that disappear need not have a path to every later time. -/
structure M71FiniteContinuationService
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    (ancestry : RepairedFiniteAncestryData D.flow W) where
  identification_system : M59IdentificationSystem.{u}
  basepoint_service : M59HigherBasepointTransportService
  initial : M67InitialClassData identification_system ancestry.initial_component
    (D.flow.metric 0)
  hM61 : M61WidthTheory.{u} identification_system.quotient
  hM64 : M64ComparisonTheory.{u}
  hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64
  hM58 : RepairedShortLoopTrivialityTheory.{u}
  hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65
  comparison_bounds : M67EventComparisonBounds D.flow Set.univ
  scalar_lower_bound : M67ScalarLowerBound D.flow Set.univ
  target_cover :
    ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain),
      ∃ n : ℕ,
        ∃ packages : Fin n →
          M71ComponentContinuationData D W ancestry basepoint_service T hT,
          ∀ x : (D.flow.slice T).carrier,
            ∃ i : Fin n,
              x ∈ Set.range
                ((packages i).P.component
                  ⟨T, ⟨D.flow.time_domain_nonnegative hT, le_rfl⟩⟩).inclusion

/-- Primitive input for the global extinction theorem.  The equality identifies
the repaired flow used by M56/M70 with the exact M52 certificate flow. -/
structure M71GlobalExtinctionInput
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (N : NormalizedInitialMetric (M := M))
    (G : RepairedGlobalFlowData N) where
  g₀ : StandardInitialMetric
  D : RepairedSurgeryFlowData.{u} g₀
  flow_eq : D.flow = G.certificate.flow
  W : RepairedEventChildWitness D.flow
  ancestry : RepairedFiniteAncestryData D.flow W
  initial_connected : IsConnected (Set.univ : Set M)
  initial_group : ∀ x : (D.flow.slice 0).carrier,
    IsFiniteFreeProductCyclic (FundamentalGroup (D.flow.slice 0).carrier x)
  continuation : M71FiniteContinuationService D W ancestry

end PoincareMT
