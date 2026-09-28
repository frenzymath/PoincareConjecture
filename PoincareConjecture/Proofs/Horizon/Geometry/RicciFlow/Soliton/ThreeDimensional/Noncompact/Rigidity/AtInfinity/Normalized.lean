import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.AtInfinity.Line
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.AtInfinity.ScalarTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Normalization.Flow








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)
  {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

theorem unscaledPointedLimit_metricKappaNoncollapsed
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0))
    (t : ℝ) (ht : t < 1) :
    MetricKappaNoncollapsed (L.limitFlow.metric t) (L.limitFlow.connection t) S.kappa := by
  refine ⟨S.kappa_pos, ?_⟩
  have hvol := L.ball_volume_lower_bound_of_static_source_noncollapse
    (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (n := 3) (M := M))
    (fun _ => G.unscaledSourceFlow.shrink) t ht
    (G.unscaledPointedLimit_complete L hcomplete t ht) S.kappa (by
      intro k x r hr hbound
      have hκ := G.unscaledSourceFlow.metricKappaNoncollapsed_shrink t
        (G.unscaledSourceFlow_metricKappaNoncollapsed t ht)
      simpa only [AncientRescalingSequence.smallRescalingCarrier,
        calibratedMetricVolume_eq_volumeMeasure] using hκ.2 x r hr hbound)
  simpa only [calibratedMetricVolume_eq_volumeMeasure] using hvol


def unscaledLiftedCarrier : FlowCarrier.{u} 3 := by
  let C := L.limitCarrier
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) C.carrier
  let : ConnectedSpace (ULift.{u} C.carrier) :=
    (Homeomorph.ulift.connectedSpace_iff).mpr inferInstance
  let : SecondCountableTopology (ULift.{u} C.carrier) :=
    Homeomorph.ulift.secondCountableTopology
  exact FlowCarrier.ofConnectedManifold 3 (ULift.{u} C.carrier)


def unscaledLiftedFlow : RicciFlow 3 (G.unscaledLiftedCarrier L).carrier (Iio 1) :=
  L.limitFlow.ulift

theorem unscaledLiftedFlow_complete
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0)) (t : ℝ) (ht : t < 1) :
    MetricComplete ((G.unscaledLiftedFlow L).metric t) :=
  (L.limitFlow.ulift_metricComplete_iff t).mpr (G.unscaledPointedLimit_complete L hcomplete t ht)

theorem unscaledLiftedFlow_nonnegativeCurvatureOperator (t : ℝ) (ht : t < 1)
    (x : (G.unscaledLiftedCarrier L).carrier) :
    ((G.unscaledLiftedFlow L).connection t).NonnegativeCurvatureOperator x :=
  (L.limitFlow.ulift_nonnegativeCurvatureOperator_iff t x).mpr
    (G.unscaledPointedLimit_nonnegativeCurvatureOperator L t ht x.down)

theorem unscaledLiftedFlow_past_curvature_bound (T : ℝ) (hT : T < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ≤ T, ∀ x : (G.unscaledLiftedCarrier L).carrier,
      ((G.unscaledLiftedFlow L).connection t).curvatureTensorNorm x ≤ B := by
  obtain ⟨B, hB, hbound⟩ := G.unscaledPointedLimit_curvature_bound L
  refine ⟨B / (1 - T), div_nonneg hB (sub_pos.mpr hT).le, fun t ht x => ?_⟩
  have h := (hbound t (ht.trans_lt hT) x.down).trans
    (div_le_div_of_nonneg_left hB (sub_pos.mpr hT) (by linarith))
  simpa only [unscaledLiftedFlow, L.limitFlow.ulift_curvatureTensorNorm] using h

theorem unscaledLiftedFlow_metricKappaNoncollapsed
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0)) (t : ℝ) (ht : t < 1) :
    MetricKappaNoncollapsed ((G.unscaledLiftedFlow L).metric t)
      ((G.unscaledLiftedFlow L).connection t) S.kappa := by
  let : ConnectedSpace L.limitCarrier.carrier := connectedSpace_iff_univ.mpr L.limitCarrier.connected
  exact L.limitFlow.metricKappaNoncollapsed_ulift t
    (G.unscaledPointedLimit_metricKappaNoncollapsed L hcomplete t ht)

theorem unscaledLiftedFlow_line (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0)) (t : ℝ) (ht : t < 1) :
    ∃ γ : ℝ → (G.unscaledLiftedCarrier L).carrier, ∀ s r : ℝ,
      ((G.unscaledLiftedFlow L).metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r| := by
  let := L.limitCarrier.metricSpaceOf (L.limitFlow.metric t)
  obtain ⟨γ, hγ, _⟩ := G.unscaledPointedLimit_line p q hescape L hcomplete t ht
  refine ⟨fun s => ULift.up.{u} (γ s), fun s r => ?_⟩
  rw [show ((G.unscaledLiftedFlow L).metric t).edist
      (ULift.up.{u} (γ s)) (ULift.up.{u} (γ r)) =
      (L.limitFlow.metric t).edist (γ s) (γ r) from L.limitFlow.ulift_edist t _ _]
  change edist (γ s) (γ r) = _
  rw [hγ.edist_eq, edist_dist, Real.dist_eq]

theorem unscaledLiftedFlow_scalar_lower_bound (hC : RicciFlowCurvatureTheory.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ t < 1, ∀ x : (G.unscaledLiftedCarrier L).carrier,
      c / (1 - t) ≤ ((G.unscaledLiftedFlow L).connection t).scalarCurvature x := by
  obtain ⟨c, hc, hbound⟩ := G.unscaledPointedLimit_scalar_lower_bound hC q L
  refine ⟨c, hc, fun t ht x => ?_⟩
  simpa only [unscaledLiftedFlow, L.limitFlow.ulift_scalarCurvature] using hbound t ht x.down



theorem unscaledPointedLimit_scalarCurvature_eq_one_div_one_sub
    (hP : ThreeDimensionalClassificationPredecessors.{u}) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0)) :
    ∀ t < 1, ∀ x : L.limitCarrier.carrier,
      (L.limitFlow.connection t).scalarCurvature x = 1 / (1 - t) := by
  let : ConnectedSpace (G.unscaledLiftedCarrier L).carrier :=
    connectedSpace_iff_univ.mpr (G.unscaledLiftedCarrier L).connected
  obtain ⟨c, hc, hlower⟩ := G.unscaledLiftedFlow_scalar_lower_bound L hP.curvature
  have h := (G.unscaledLiftedFlow L).scalarCurvature_eq_one_div_one_sub_of_line_at_each_time
    hP (G.unscaledLiftedFlow_complete L hcomplete)
    (G.unscaledLiftedFlow_nonnegativeCurvatureOperator L)
    (G.unscaledLiftedFlow_past_curvature_bound L)
    (G.unscaledLiftedFlow_metricKappaNoncollapsed L hcomplete)
    (G.unscaledLiftedFlow_line L p hescape hcomplete) hc hlower
  intro t ht x
  simpa only [unscaledLiftedFlow, L.limitFlow.ulift_scalarCurvature] using h t ht (ULift.up.{u} x)

theorem unscaledSourceFlow_scalarCurvature_zero (x : M) :
    (G.unscaledSourceFlow.connection 0).scalarCurvature x = S.connection.scalarCurvature x := by
  exact (G.unscaledSourceFlow.connection 0).scalarCurvature_eq_of_local_isometry
    S.connection (f := id) isOpen_univ contMDiff_id.contMDiffOn
    (by
      intro y _ v w
      simp only [G.unscaledSourceFlow_metric_zero, mfderiv_id, ContinuousLinearMap.id_apply, id_eq])
    (mem_univ x)

include G in
omit L in


theorem exists_scalar_subsequence_tendsto_one
    (hP : ThreeDimensionalClassificationPredecessors.{u}) (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun k => S.connection.scalarCurvature (q (σ k))) atTop (𝓝 1) := by
  obtain ⟨L, hcomplete⟩ := G.exists_unscaledPointedLimit hP.curvature q
  have hnormalized : (L.limitFlow.connection 0).scalarCurvature L.base = 1 := by
    simpa only [sub_zero, div_one] using
      G.unscaledPointedLimit_scalarCurvature_eq_one_div_one_sub L hP p hescape hcomplete
        0 (by norm_num) L.base
  have hscalar := L.tendsto_scalarCurvature
    (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (n := 3) (M := M))
    (fun _ => G.unscaledSourceFlow.shrink) (by norm_num : (0 : ℝ) < 1)
    0 (by norm_num) L.base
  rw [hnormalized] at hscalar
  refine ⟨L.subsequence, L.subsequence_strictMono, ?_⟩
  simpa only [L.base_preserving, G.unscaledSourceFlow.shrink_scalarCurvature, Equiv.symm_apply_apply,
    G.unscaledSourceFlow_scalarCurvature_zero] using hscalar

end PoincareConjecture.ShrinkingSolitonFlow

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem GradientShrinkingSolitonData.exists_scalar_subsequence_tendsto_one
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u}) (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun k => S.connection.scalarCurvature (q (σ k))) atTop (𝓝 1) := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  exact G.exists_scalar_subsequence_tendsto_one hP p q hescape

end PoincareConjecture
