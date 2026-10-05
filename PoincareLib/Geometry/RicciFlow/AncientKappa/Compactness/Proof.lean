import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Estimates
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Construction
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Convergence
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Terminal
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.SpatialBounds
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Embeddings
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Normalized
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Noncollapse
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Nonflatness
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.ParabolicNoncollapse
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.ScalarBuffer
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.TerminalLimit
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Limit
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.AncientSolution
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Assembly.Convergence
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Conclusion

/-!
# M23 normalized kappa compactness proof entry

The local estimate, common interior limit, actual complete terminal flow,
and convergence through zero are constructed from the explicit predecessors.
The global terminal scalar bound is proved on that actual flow before it is
packaged as an ancient kappa-solution.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance compactnessProofConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

/- The global curvature clause is already part of the ancient-solution
structure.  Keeping this adapter explicit prevents the M23 construction from
re-proving a bound which is inherited once the actual limit is identified. -/
theorem m23LimitBoundedCurvature_of_limit
    {kappa : ℝ} (B : BasedKappaSolution kappa) :
    M23LimitBoundedCurvature B := by
  let C := B.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := B.connectedSpace
  change ∀ t : ℝ, t ≤ 0 → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : C.carrier,
    |(B.flow.flow.connection t).curvatureTensorNorm x| ≤ K
  intro t ht
  exact B.flow.bounded_curvature t ht

/-- M23: Fix a positive constant kappa and a sequence of based, complete,
nonflat, nonnegatively curved three-dimensional kappa-solutions whose
basepoints satisfy R(p_k,0)=1. Given the actual M04, M07, M13, M16, M19,
M21 and M22 services, produce a strictly increasing subsequence converging
smoothly, including time zero, to a based ancient solution with the same
kappa. For each positive r, one constant bounds R(q,0) for every index and
every q in its terminal radius-r base ball. Retain the resulting whole-past
full-curvature bounds on those balls and bounded curvature of each limit slice.
Compact and nonorientable inputs are included.

The same terminal embedding family preserves ordinary time lines, agrees
with the interior maps, preserves the terminal basepoint, and gives uniform
convergence of all metric jets on compact sets meeting zero. Derivatives
are taken within the fixed past half-space. The limit is complete,
noncollapsed with the original kappa, and scalar-normalized at zero.

M23 constructs the finite-window hypotheses, calibrated volume comparisons,
point-picked rescalings, terminal maps and completeness, mixed jets and
limit noncollapse. Its fixed-radius volume-collapse contradiction uses M21
on actual input solutions and M22 only after a bounded nonflat auxiliary
kappa-solution exists. M04 scalar-zero rigidity handles the raw flat limit.
This treats compact inputs without the printed proof's noncompact threshold.

For the final generic limit, first construct a separately bounded blow-up
and its actual two-dimensional factor, then apply M19. Shrinking
spherical or projective necks in one fixed original slice contradict the
nonnegative-curvature convex-exhaustion argument. Bounds and every-time
nonflatness are proved
before the original limit is packaged as a kappa-solution. These are internal
proof obligations, not hypotheses asserting the desired limit or its bounds.

Sources: Morgan--Tian Theorem 9.64, pp. 225/229; Lemma 9.65 and Claim 9.66,
pp. 225-227; Proposition 9.60 and Corollaries 9.62-9.63, pp. 222-225;
Definition 5.12 and Theorems 5.11/5.15, pp. 89-92; Theorem 3.28,
pp. 51-52; Theorem 4.18, p. 71; Corollary 9.50, pp. 213-214.
The generic-limit completion uses corrected Kleiner--Lott Theorem 46.1,
pp. 2687-2688, including its nonnegative-curvature neck obstruction.
The 2015 Section 19.2 correction does not affect these Chapter 9 results.

The source distinctions and existing compactness, endpoint, Harnack and
bounded-limit corrections are recorded in
reviews/errata/2026-09-15-m23-compactness.md and the full derivations in
reviews/contracts/2026-09-15-m23-complete-contract.md. The checked producers
are in Proofs/M23/Providers.lean; the M19 and M22 fields have their actual
earlier prerequisites supplied there. -/
theorem m23NormalizedKappaCompactness
    (N : NormalizedKappaCompactnessData)
    (P : M23NormalizedKappaCompactnessPredecessors) :
    Nonempty (RedesignNormalizedKappaCompactnessConclusion N) := by
  classical
  have hlocal : M23LocalCurvatureEstimate N.sequence :=
    m23LocalCurvatureEstimate_of_predecessors N.sequence P
  have hcontrol := m23AllTimeCurvatureControl_of_local N.sequence P hlocal
  obtain ⟨H, F, hF, hcomplete, hoperator, hnc, hnormalized, hmono, hpast⟩ :=
    N.sequence.exists_complete_noncollapsed_closed_geometric_limit P hlocal
  have hbounded : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : H.limitCarrier.carrier, (F.connection 0).scalarCurvature x ≤ B := by
    exact F.exists_terminal_scalar_bound_of_m23_predecessors P N.sequence.kappa_pos
      hcomplete hoperator hmono
      (fun t ht p r hr hcurv => hnc r hr t ht p r hr le_rfl hcurv) H.base
  obtain ⟨B, hB, hbound⟩ := hbounded
  have hpositive : ∃ x : H.limitCarrier.carrier,
      0 < (F.connection 0).scalarCurvature x :=
    ⟨H.base, by rw [hnormalized]; norm_num⟩
  let K := F.ancientKappaSolutionOfTerminalScalarBound P N.sequence.kappa_pos hB
    hcomplete hoperator hnc hpositive (fun t ht x => hpast t 0 ht le_rfl x) hbound
  have hreference : H.limitCarrier.metricComplete (H.limitFlow.metric 0) := by
    have h := hcomplete (-1) (by norm_num)
    rw [hF (-1) (by norm_num)] at h
    simpa only [neg_add_cancel] using h
  obtain ⟨G, hterminal⟩ :=
    N.sequence.exists_interiorConvergence_terminalExtension_of_ancient_limit
      H K rfl hnormalized hF P hcontrol hreference
  exact ⟨{
    convergence := G
    local_curvature_estimate := hlocal
    all_time_curvature_control := hcontrol
    limit_bounded_curvature := m23LimitBoundedCurvature_of_limit G.limit
    terminal_extension := hterminal
  }⟩

/-! Downstream imports use the same named theory wrapper. -/
theorem m23NormalizedKappaCompactnessConclusionTheory
    (N : NormalizedKappaCompactnessData)
    (P : M23NormalizedKappaCompactnessPredecessors) :
    Nonempty (RedesignNormalizedKappaCompactnessConclusion N) :=
  m23NormalizedKappaCompactness N P

end PoincareMT
