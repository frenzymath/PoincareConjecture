import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.PointSelection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RescaledSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.Line
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SmallRescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallBuffer














noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold
  uliftSecondCountable uliftConnected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

set_option maxHeartbeats 800000 in



theorem exists_nonflat_ancient_blowup_limit_of_unbounded_scalarCurvature_lt
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    {t₀ : ℝ} (ht₀ : t₀ < 0) (p : L.convergence.limit.carrier.carrier)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t₀).scalarCurvature))
    {η : ℝ} (hη : 0 < η) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    ∃ (q : ℕ → L.convergence.limit.carrier.carrier) (r : ℕ → ℝ)
      (hQ : ∀ i, 0 < (L.convergence.limit.flow.connection t₀).scalarCurvature (q i)),
      let F := L.convergence.limit.flow
      let Q := fun i => (F.connection t₀).scalarCurvature (q i)
      let R := fun i => r i * Real.sqrt (Q i)
      let H := fun i =>
        (F.ulift : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).openAncientRescaleAt
          (Q i) (hQ i) t₀
      (∀ i, 0 < r i ∧
        (∀ x ∈ (F.metric t₀).ball (q i) (r i), (F.connection t₀).scalarCurvature x ≤ 4 * Q i) ∧
        ∀ s ≤ t₀, ∀ x ∈ (F.metric t₀).ball (q i) (r i),
          (F.connection s).curvatureTensorNorm x ≤ 36 * Q i) ∧
      Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop ∧
      Tendsto Q atTop atTop ∧ Tendsto R atTop atTop ∧
      Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal * Real.sqrt (Q i)) atTop atTop ∧
      Tendsto (fun i => r i / ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 0) ∧
      (∀ i, ((H i).connection 0).scalarCurvature (ULift.up (q i)) = 1) ∧
      ∃ ν : ℝ, 0 < ν ∧
        (∀ᶠ i in atTop, ENNReal.ofReal ν ≤
          ((H i).metric 0).volumeMeasure (((H i).metric 0).ball (ULift.up (q i)) 1)) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < η ∧
          ∃ G : AncientPointedGeometricConvergence
            (fun _ => (FlowCarrier.ofConnectedManifold 3
              (ULift.{u} L.convergence.limit.carrier.carrier)).shrink)
            (fun i t => (H i).shrink.metric (t - δ))
            (fun i => equivShrink (ULift.{u} L.convergence.limit.carrier.carrier)
              (ULift.up (q i))) δ,
            (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
            (1 / 2 : ℝ) ≤ 9 * (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
            (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
             (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
               (G.limitFlow.connection t).curvatureTensorNorm x ≤ 36) ∧
             (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
               (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
             (letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
              ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base)) := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  obtain ⟨q, r, hcontrol, hd, hQtendsto, hR, hdQ, hratio⟩ :=
    L.exists_escaping_backward_controlled_sequence_of_unbounded_curvature hC ht₀ p hunbounded
  let F := L.convergence.limit.flow
  let V : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  have hQ (i : ℕ) : 0 < (F.connection t₀).scalarCurvature (q i) := (hcontrol i).1
  let Q := fun i => (F.connection t₀).scalarCurvature (q i)
  let R := fun i => r i * Real.sqrt (Q i)
  let H := fun i => V.openAncientRescaleAt (Q i) (hQ i) t₀
  have htime (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) : t₀ + s / Q i < 0 := by
    have h := (div_lt_iff₀ (hQ i)).mpr hs
    linarith
  have hwindow (i : ℕ) (a : ℝ) : Icc a 0 ⊆ interior (Iio (-t₀ * Q i)) := by
    rw [isOpen_Iio.interior_eq]
    intro s hs
    exact hs.2.trans_lt (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hcompleteH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) :
      MetricComplete ((H i).metric s) := by
    apply V.parabolicRescale_metricComplete
    exact (F.ulift_metricComplete_iff _).mpr (L.convergence.limit.complete _ (htime i s hs))
  have hoperatorH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i))
      (x : ULift.{u} L.convergence.limit.carrier.carrier) :
      ((H i).connection s).NonnegativeCurvatureOperator x := by
    apply V.parabolicRescale_nonnegativeCurvatureOperator
    exact (F.ulift_nonnegativeCurvatureOperator_iff _ x).mpr
      (L.convergence.limit.nonnegative_curvature_operator _ (htime i s hs) x.down)
  have hball (i : ℕ) : ((H i).metric 0).ball (ULift.up (q i)) (R i) =
      (V.metric t₀).ball (ULift.up (q i)) (r i) := by
    change (rescaledMetric (V.metric (t₀ + 0 / Q i)) (Q i) (hQ i)).ball _ _ = _
    rw [rescaledMetric_ball_allDimensions, zero_div, add_zero]
    dsimp only [R]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (hQ i)).ne']
  have hscalarH (i : ℕ) (s : ℝ) (hs : s ≤ 0)
      (x : ULift.{u} L.convergence.limit.carrier.carrier)
      (hx : x ∈ ((H i).metric 0).ball (ULift.up (q i)) (R i)) :
      ((H i).connection s).scalarCurvature x ≤ 4 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have hx' : x.down ∈ (F.metric t₀).ball (q i) (r i) := by
      have := (hball i) ▸ hx
      simpa only [RiemannianMetric.ball, Set.mem_ofPred_eq, V, F.ulift_edist] using this
    have hscalar := (L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
      L.scalar_curvature_nonnegative_time_derivative x.down (hst.trans_lt ht₀) ht₀ hst).trans
        ((hcontrol i).2.2.1 x.down hx')
    dsimp only [H, RicciFlow.openAncientRescaleAt]
    rw [RicciFlow.parabolicRescale_scalarCurvature, F.ulift_scalarCurvature]
    have h := mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (hQ i).le)
    calc
      _ ≤ (Q i)⁻¹ * (4 * Q i) := h
      _ = 4 := by rw [← mul_assoc, mul_comm _ 4, mul_assoc, inv_mul_cancel₀ (hQ i).ne', mul_one]
  have hnormalize (i : ℕ) :
      ((H i).connection 0).scalarCurvature (ULift.up (q i)) = 1 := by
    dsimp only [H, RicciFlow.openAncientRescaleAt]
    rw [RicciFlow.parabolicRescale_scalarCurvature, zero_div, add_zero, F.ulift_scalarCurvature]
    exact inv_mul_cancel₀ (hQ i).ne'
  have hκ := L.convergence.limit.metricKappaNoncollapsed_of_scalar_derivative_nonnegative
    hC K.kappa_pos L.kappa_noncollapsed L.scalar_curvature_nonnegative_time_derivative ht₀
  have hκH (i : ℕ) : MetricKappaNoncollapsed ((H i).metric 0) ((H i).connection 0)
      (K.kappa / 729) := by
    change MetricKappaNoncollapsed
      (rescaledMetric (V.metric (t₀ + 0 / Q i)) (Q i) (hQ i))
      (rescaledMetric_connection (V.metric (t₀ + 0 / Q i))
        (V.connection (t₀ + 0 / Q i)) (Q i) (hQ i)) (K.kappa / 729)
    rw [show t₀ + 0 / Q i = t₀ by simp]
    exact
      (F.metricKappaNoncollapsed_ulift t₀ hκ :
        MetricKappaNoncollapsed (V.metric t₀) (V.connection t₀) (K.kappa / 729)).rescaledMetric
          (Q i) (hQ i)
  let ν := (K.kappa / 729) * (1 / 6 : ℝ) ^ 3
  have hν : 0 < ν := mul_pos (div_pos K.kappa_pos (by norm_num)) (by norm_num)
  have hvolume : ∀ᶠ i in atTop, ENNReal.ofReal ν ≤
      ((H i).metric 0).volumeMeasure (((H i).metric 0).ball (ULift.up (q i)) 1) := by
    filter_upwards [hR.eventually_ge_atTop (1 / 6 : ℝ)] with i hi
    have hsmall := (hκH i).2 (ULift.up (q i)) (1 / 6) (by norm_num) (by
      intro x hx
      have hxR : x ∈ ((H i).metric 0).ball (ULift.up (q i)) (R i) :=
        lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hi)
      have hx' : x.down ∈ (F.metric t₀).ball (q i) (r i) := by
        have := (hball i) ▸ hxR
        simpa only [RiemannianMetric.ball, Set.mem_ofPred_eq, V, F.ulift_edist] using this
      have hb := (hcontrol i).2.2.2 t₀ le_rfl x.down hx'
      change |(rescaledMetric_connection (V.metric (t₀ + 0 / Q i))
        (V.connection (t₀ + 0 / Q i)) (Q i) (hQ i)).curvatureTensorNorm x| ≤ _
      rw [rescaledMetric_curvatureTensorNorm_exact, zero_div, add_zero,
        F.ulift_curvatureTensorNorm, abs_mul, abs_of_pos (inv_pos.mpr (hQ i))]
      have hnonneg : 0 ≤ (F.connection t₀).curvatureTensorNorm x.down := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnonneg]
      have := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hQ i).le)
      calc
        _ ≤ (Q i)⁻¹ * (36 * Q i) := this
        _ = 36 * ((Q i)⁻¹ * Q i) := by ring
        _ = (1 / 6 : ℝ)⁻¹ ^ 2 := by rw [inv_mul_cancel₀ (hQ i).ne']; norm_num)
    rw [calibratedMetricVolume_eq_volumeMeasure] at hsmall
    exact hsmall.trans (MeasureTheory.measure_mono
      (fun _ hx => lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 6 : ℝ) ≤ 1))))
  let A : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hA : Tendsto A atTop atTop := tendsto_atTop_mono
    (fun i => show (i : ℝ) ≤ A i by dsimp [A]; linarith) tendsto_natCast_atTop_atTop
  obtain ⟨δ, hδ, hδone, hδη, G, hGcomplete, hquant, hnonflat, hGnorm, hGoperator⟩ :=
    RicciFlow.exists_nonflat_ancient_limit_of_small_expanding_cylinders_quantitative_lt
      hC (by norm_num : 0 < 2)
      (fun _ => FlowCarrier.ofConnectedManifold 3 (ULift.{u} L.convergence.limit.carrier.carrier))
      (fun i => Iio (-t₀ * Q i)) H (fun i => ULift.up (q i)) A R hA hR
      (fun i => hwindow i (-A i))
      (fun i s hs => hcompleteH i s (interior_subset (hwindow i (-A i) hs)))
      (fun i s hs => hoperatorH i s (interior_subset (hwindow i (-A i) hs)))
      (fun i s hs => hscalarH i s hs.2) hnormalize hν hvolume hη
  have hmonotoneV (x : ULift.{u} L.convergence.limit.carrier.carrier) :
      MonotoneOn (fun t => (V.connection t).scalarCurvature x) (Iio 0) := by
    intro s hs t ht hst
    simpa only [V, F.ulift_scalarCurvature] using
      L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
        L.scalar_curvature_nonnegative_time_derivative x.down hs ht hst
  have hscalarV (i : ℕ) (x : ULift.{u} L.convergence.limit.carrier.carrier)
      (hx : x ∈ (V.metric t₀).ball (ULift.up (q i)) (r i)) :
      (V.connection t₀).scalarCurvature x ≤ 4 * Q i := by
    rw [F.ulift_scalarCurvature]
    apply (hcontrol i).2.2.1 x.down
    simpa only [RiemannianMetric.ball, Set.mem_ofPred_eq, V, F.ulift_edist] using hx
  have hline := V.exists_isometric_line_of_open_selected_rescalings hC (by norm_num : 0 < 2)
    (fun t ht => (F.ulift_metricComplete_iff t).mpr (L.convergence.limit.complete t ht))
    (fun t ht x => (F.ulift_nonnegativeCurvatureOperator_iff t x).mpr
      (L.convergence.limit.nonnegative_curvature_operator t ht x.down))
    hmonotoneV t₀ ht₀ (ULift.up p) (fun i => ULift.up (q i)) r Q
    (fun i => (hcontrol i).2.1) hQ hscalarV
    (by simpa only [V, F.ulift_edist] using hd)
    (by simpa only [V, F.ulift_edist] using hdQ) hR
    (by simpa only [V, F.ulift_edist] using hratio) hδ G (hGcomplete 0 hδ)
  refine ⟨q, r, hQ, (fun i => (hcontrol i).2), hd, hQtendsto, hR, hdQ, hratio,
    hnormalize, ν, hν, hvolume, δ, hδ, hδone, hδη, G, hGcomplete,
    by norm_num at hquant ⊢; exact hquant, hnonflat, ?_, hGoperator, hline⟩
  norm_num at hGnorm ⊢
  exact hGnorm

end AncientAsymptoticSolitonLimitData

end PoincareConjecture
