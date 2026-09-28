import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.SmallRadiusRescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.EarlierVolumeUpper
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Unnormalized.Volume











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance volumeDeficitCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)



theorem exists_complete_flat_slice_with_volume_deficit
    (P : M23NormalizedKappaCompactnessPredecessors) (hn : ¬ M23LocalCurvatureEstimate S) :
    ∃ (C : FlowCarrier.{0} 3) (g : RiemannianMetric 3 C.carrier)
      (D : LeviCivitaData g) (p : C.carrier),
      C.metricComplete g ∧ (∀ x, D.curvatureTensorNorm x = 0) ∧
      (∀ r : ℝ, 0 < r → ENNReal.ofReal (κ * r ^ 3) ≤
        calibratedMetricVolume g (g.ball p r)) ∧
      calibratedMetricVolume g (g.ball p 1) ≤
        ENNReal.ofReal ((3 / 4) * RiemannianMetric.euclideanUnitBallVolume 3) := by
  obtain ⟨j, ρ, K, _, _, hkappa, _, hunit, _, hscalar, hcontrol⟩ :=
    S.exists_small_radius_rescaled_sequence_of_not_localCurvatureEstimate P hn
  let C (k : ℕ) := (S.term (j k)).carrier
  let p (k : ℕ) : (C k).carrier := (S.term (j k)).base
  obtain ⟨G, hcomplete, _⟩ :=
    AncientKappaSequence.exists_complete_nonnegative_interior_geometric_limit C K p P
      S.kappa_pos hkappa hcontrol
  obtain ⟨B, hB, hbound⟩ := hcontrol 1 (by norm_num)
  obtain ⟨δ, hδ, hδ1, hvolume⟩ :=
    AncientKappaSequence.exists_earlier_half_euclidean_unit_ball_volume_bound
      C K p P hB hbound hunit
  have hs : 1 - δ < 1 := by linarith
  refine ⟨G.limitCarrier, G.limitFlow.metric (1 - δ), G.limitFlow.connection (1 - δ),
    G.base, hcomplete _ hs, ?_, ?_, ?_⟩
  · exact AncientKappaSequence.interiorLimit_flat_of_base_scalar_tendsto_zero
      C K p G P hscalar _ hs
  · intro r hr
    exact AncientKappaSequence.interiorLimit_ball_volume_ge_of_base_scalar_tendsto_zero
      C K p G P hkappa hcomplete hscalar hs G.base hr
  · apply AncientKappaSequence.interiorLimit_ball_volume_le C K p G hs
      (by norm_num : (0 : ℝ) < 1) (hcomplete _ hs)
    exact Eventually.of_forall fun k => by
      have htime : (1 - δ) - 1 = -δ := by ring
      rw [htime]
      exact hvolume k

end PoincareConjecture.NormalizedKappaSolutionSequence
