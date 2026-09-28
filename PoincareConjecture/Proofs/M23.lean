import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.SpatialBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Nonflatness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ParabolicNoncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ScalarBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.TerminalLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.AncientSolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Assembly.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Conclusion

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance compactnessProofConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

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

theorem m23NormalizedKappaCompactnessConclusionTheory
    (N : NormalizedKappaCompactnessData)
    (P : M23NormalizedKappaCompactnessPredecessors) :
    Nonempty (RedesignNormalizedKappaCompactnessConclusion N) :=
  m23NormalizedKappaCompactness N P

end PoincareConjecture
