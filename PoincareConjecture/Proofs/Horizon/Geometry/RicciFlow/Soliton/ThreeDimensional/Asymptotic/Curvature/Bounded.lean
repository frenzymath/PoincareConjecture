import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SmallNecks
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Scale

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold uliftConnected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem bddAbove_scalarCurvature
    (P : ThreeDimensionalClassificationPredecessors.{u})
    (L : AncientAsymptoticSolitonLimitData S) (t : ℝ) (ht : t < 0) :
    BddAbove (range (L.convergence.limit.flow.connection t).scalarCurvature) := by
  classical
  by_contra hunbounded
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let F := L.convergence.limit.flow
  let G : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  obtain ⟨ε, hε, hεhalf, hscale⟩ :=
    RiemannianMetric.exists_universal_neck_scale_lower_bound.{u}
  obtain ⟨ρ, hρ, hlower⟩ := hscale _ (G.metric t) (G.connection t)
    ((F.ulift_metricComplete_iff t).mpr (L.convergence.limit.complete t ht))
    (L.ulift_strictlyPositiveSectionalCurvature_of_unbounded_scalarCurvature
      P.curvature t ht hunbounded) ε hε le_rfl
  obtain ⟨N, hepsilon, hsmall⟩ :=
    L.exists_small_neck_of_unbounded_scalarCurvature P ht hunbounded hε hεhalf hρ
  exact (not_lt_of_ge (hlower N hepsilon)) hsmall

theorem bounded_curvature_threeDimensional
    (P : ThreeDimensionalClassificationPredecessors.{u})
    (L : AncientAsymptoticSolitonLimitData S) (t : ℝ) (ht : t < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.convergence.limit.carrier.carrier,
      |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B := by
  exact (L.convergence.limit.bddAbove_scalarCurvature_iff_bounded_curvature
    P.curvature t ht).mp (L.bddAbove_scalarCurvature P t ht)

end PoincareConjecture.AncientAsymptoticSolitonLimitData
