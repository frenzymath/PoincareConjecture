import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Small
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

theorem compact_uniform_normalized_scalar_bound
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa r : ℝ} (hkappa : 0 < kappa) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : BasedKappaSolution kappa,
      ∀ x ∈ (B.flow.flow.metric 0).ball B.base r,
        (B.flow.flow.connection 0).scalarCurvature x ≤ C := by
  classical
  by_contra h
  push Not at h
  have hbad (k : ℕ) : ∃ B : BasedKappaSolution kappa,
      ∃ x ∈ (B.flow.flow.metric 0).ball B.base r,
        (k : ℝ) + 1 < (B.flow.flow.connection 0).scalarCurvature x :=
    h ((k : ℝ) + 1) (by positivity)
  choose B x hx hscalar using hbad
  let S : NormalizedKappaSolutionSequence kappa := ⟨hkappa, B⟩
  obtain ⟨L⟩ := P.normalized_compactness ⟨kappa, hkappa, S⟩
  obtain ⟨C, _, hC⟩ := L.local_curvature_estimate r hr
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hbound := hC k (x k) (hx k)
  have hlarge := hscalar k
  dsimp [S] at hbound
  linarith

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

theorem compact_uniform_scalar_bound_of_normalized
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa r : ℝ} (hkappa : 0 < kappa) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ∀ x ∈ (K.flow.metric 0).ball p r,
          (K.flow.connection 0).scalarCurvature x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := compact_uniform_normalized_scalar_bound P hkappa hr
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnoncollapsed hnormalized x hx
  let : T2Space (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).t2Space
  let : SecondCountableTopology (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).symm.isEmbedding.secondCountableTopology
  have hconnected : IsConnected (Set.univ : Set (Shrink.{0} M)) := by
    simpa only [Set.image_univ, EquivLike.range_eq_univ] using
      isConnected_univ.image (Poincare.Topology.SecondCountable.homeomorphShrink M)
        (Poincare.Topology.SecondCountable.homeomorphShrink M).continuous.continuousOn
  let : ConnectedSpace (Shrink.{0} M) := connectedSpace_iff_univ.mpr hconnected
  let Ks : AncientKappaSolution 3 (Shrink.{0} M) := {
    flow := K.flow.shrink
    kappa := kappa
    kappa_pos := hkappa
    complete := fun t ht ↦ (K.flow.shrink_metricComplete_iff t).mpr (K.complete t ht)
    nonnegative_curvature_operator := fun t ht y ↦
      (K.flow.shrink_nonnegativeCurvatureOperator_iff t y).mpr
        (K.nonnegative_curvature_operator t ht ((equivShrink M).symm y))
    bounded_curvature := by
      intro t ht
      obtain ⟨D, hD, hbound⟩ := K.bounded_curvature t ht
      refine ⟨D, hD, fun y ↦ ?_⟩
      simpa only [RicciFlow.shrink_curvatureTensorNorm] using
        hbound ((equivShrink M).symm y)
    nonflat := by
      intro t ht
      obtain ⟨y, hy⟩ := K.nonflat t ht
      exact ⟨equivShrink M y, by simpa only [RicciFlow.shrink_curvatureTensorNorm,
        Equiv.symm_apply_apply] using hy⟩
    noncollapsed := by
      intro r0 hr0 t ht q s hs hsr0 hcurv
      rw [calibratedMetricVolume_eq_volumeMeasure, RicciFlow.shrink_volumeMeasure_ball,
        ← calibratedMetricVolume_eq_volumeMeasure]
      apply hnoncollapsed r0 hr0 t ht ((equivShrink M).symm q) s hs hsr0
      intro a ha y hy
      have hy' : equivShrink M y ∈ (K.flow.shrink.metric t).ball q s := by
        change (K.flow.shrink.metric t).edist q (equivShrink M y) < _
        simpa only [RicciFlow.shrink_edist, Equiv.symm_apply_apply,
          RiemannianMetric.ball, Set.mem_ofPred_eq] using hy
      simpa only [RicciFlow.shrink_curvatureTensorNorm, Equiv.symm_apply_apply] using
        hcurv a ha (equivShrink M y) hy'
  }
  let Crr : FlowCarrier 3 := {
    carrier := Shrink.{0} M
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := inferInstance
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := inferInstance
    connected := hconnected
  }
  let B : BasedKappaSolution kappa := {
    carrier := Crr
    connectedSpace := inferInstance
    flow := Ks
    base := equivShrink M p
    kappa_eq := rfl
    scalar_normalized := by
      change (K.flow.shrink.connection 0).scalarCurvature (equivShrink M p) = 1
      rw [RicciFlow.shrink_scalarCurvature, Equiv.symm_apply_apply]
      exact hnormalized
  }
  have hx' : equivShrink M x ∈ (B.flow.flow.metric 0).ball B.base r := by
    change (K.flow.shrink.metric 0).edist (equivShrink M p) (equivShrink M x) < _
    simpa only [RicciFlow.shrink_edist, Equiv.symm_apply_apply,
      RiemannianMetric.ball, Set.mem_ofPred_eq] using hx
  have hresult := hbound B (equivShrink M x) hx'
  change (K.flow.shrink.connection 0).scalarCurvature (equivShrink M x) ≤ C at hresult
  simpa only [RicciFlow.shrink_scalarCurvature, Equiv.symm_apply_apply] using hresult

end PoincareConjecture
