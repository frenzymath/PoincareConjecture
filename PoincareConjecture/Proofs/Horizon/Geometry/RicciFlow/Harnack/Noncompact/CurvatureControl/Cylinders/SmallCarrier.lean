import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Small
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Universe











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance smallCarrier (M : Type u) [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] : Small.{0} M :=
  Poincare.Topology.SecondCountable.small M

noncomputable local instance smallChartedSpace {n : ℕ} (M : Type u)
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} M) :=
  Poincare.Manifold.shrinkChartedSpace _ M

local instance smallIsManifold {n : ℕ} (M : Type u) [TopologicalSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :
    IsManifold (𝓡 n) ∞ (Shrink.{0} M) :=
  Poincare.Manifold.shrinkIsManifold (𝓡 n) M

local instance smallT3Space (M : Type u) [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] : T3Space (Shrink.{0} M) :=
  (Poincare.Topology.SecondCountable.homeomorphShrink M).t3Space

noncomputable local instance smallMeasurableSpace (M : Type u)
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] :
    MeasurableSpace (Shrink.{0} M) := borel (Shrink.{0} M)

local instance smallBorelSpace (M : Type u) [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] : BorelSpace (Shrink.{0} M) := ⟨rfl⟩


noncomputable def FlowCarrier.shrink {n : ℕ} (C : FlowCarrier.{u} n) :
    FlowCarrier.{0} n where
  carrier := Shrink.{0} C.carrier
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable :=
    (Poincare.Topology.SecondCountable.homeomorphShrink C.carrier).symm.isEmbedding.secondCountableTopology
  connected := by
    simpa only [image_univ, EquivLike.range_eq_univ] using
      C.connected.image (Poincare.Topology.SecondCountable.homeomorphShrink C.carrier)
        (Poincare.Topology.SecondCountable.homeomorphShrink C.carrier).continuous.continuousOn

namespace RicciFlow



noncomputable def smallBufferedCylinderSequence
    {n : ℕ} (C : ℕ → FlowCarrier.{u} n) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow n (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (a δ : ℝ) (ha : a < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k)) : PointedFlowSequence n (a + δ) δ :=
  bufferedCylinderSequence (fun k => (C k).shrink) J (fun k => (F k).shrink)
    (fun k => equivShrink (C k).carrier (p k)) a δ ha hJ

private theorem small_hausdorff_volume_lower_bound
    {n : ℕ} (C : FlowCarrier.{0} n) (g : C.metric) (s : Set C.carrier)
    {ν : ℝ} (hν : ENNReal.ofReal ν ≤ g.volumeMeasure s) :
    ENNReal.ofReal (ν /
      (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)) : ℝ)) ≤ C.metricHausdorffVolume g s := by
  let c : ℝ≥0 := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Measure.hausdorffMeasure (n : ℝ))
  have hc : 0 < c := pos_iff_ne_zero.mpr
    (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  rw [C.volumeMeasure_eq_smul_metricHausdorffVolume] at hν
  change ENNReal.ofReal ν ≤ (c : ℝ≥0∞) * C.metricHausdorffVolume g s at hν
  change ENNReal.ofReal (ν / (c : ℝ)) ≤ C.metricHausdorffVolume g s
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hc), ENNReal.ofReal_coe_nnreal,
    ENNReal.div_le_iff (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]
  simpa only [mul_comm] using hν

set_option maxHeartbeats 800000 in


theorem exists_pointedCompactnessHypotheses_of_small_terminal_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) {a δ ν : ℝ}
    (ha : a ≤ -1) (hδ : 0 < δ) (hδone : δ ≤ 1) (hatime : a + δ < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc a 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc a 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hscalar : ∀ k, ∀ t ∈ Icc a 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ H : PointedRicciFlowCompactnessHypotheses (m + 1) (a + δ) δ,
      H.sequence = smallBufferedCylinderSequence C J F p a δ (by linarith) hJ := by
  let S := smallBufferedCylinderSequence C J F p a δ (by linarith) hJ
  have hshift {t : ℝ} (ht : t ∈ Ioo (a + δ) δ) : t - δ ∈ Icc a 0 :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hzero : -δ ∈ Icc a 0 := ⟨by linarith, by linarith⟩
  have hcurv (A : ℝ) : ∀ᶠ k in atTop,
      ∀ s ∈ Ioo (a + δ) δ, ∀ t ∈ Ioo (a + δ) δ,
        ∀ x ∈ (S.flow k).ballAt s A,
          ((S.flow k).flow.connection t).curvatureTensorNorm x ≤
            ((m + 1 : ℕ) : ℝ) ^ 2 * 4 := by
    filter_upwards [hL.eventually_ge_atTop A] with k hk
    intro s hs t ht x hx
    change ((F k).shrink.connection (t - δ)).curvatureTensorNorm x ≤ _
    rw [shrink_curvatureTensorNorm]
    apply (F k).curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder
      hC (hJ k) (hoperator k) (p k) (hscalar k) (hshift hs) (hshift ht) hk
    change ((F k).shrink.metric (s - δ)).edist
      (equivShrink (C k).carrier (p k)) x < ENNReal.ofReal A at hx
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, shrink_edist,
      Equiv.symm_apply_apply] using hx
  have hnoncollapse : ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (κ * r ^ (m + 1)) ≤ (S.flow k).zeroBallVolume r := by
    let r : ℝ := 4 * ((m + 1 : ℕ) : ℝ) + 34
    let c : ℝ≥0 := Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      (Measure.hausdorffMeasure ((m + 1 : ℕ) : ℝ))
    have hr : 0 < r := by dsimp only [r]; positivity
    have hc : 0 < c := pos_iff_ne_zero.mpr
      (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (m + 1))
    have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
    refine ⟨r, ν / (c * r ^ (m + 1)), hr, by positivity, ?_⟩
    filter_upwards [hvolume,
      hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hk hLk
    have hsub : Icc (-1 : ℝ) 0 ⊆ Icc a 0 := Icc_subset_Icc ha le_rfl
    have htransfer := (F k).terminal_unit_ball_volume_le_buffered_ball_of_cylinder
      hC hm (fun _ ht => hJ k (hsub ht))
      (fun t ht => hcomplete k t (hsub ht))
      (fun t ht => hoperator k t (hsub ht)) (p k)
      (fun t ht x hx => hscalar k t (hsub ht) x
        (hx.trans_le (ENNReal.ofReal_le_ofReal hLk)))
      (show -δ ∈ Icc (-1 : ℝ) 0 from ⟨by linarith, by linarith⟩)
    have hsmall : ENNReal.ofReal ν ≤ ((F k).shrink.metric (-δ)).volumeMeasure
        (((F k).shrink.metric (-δ)).ball (equivShrink (C k).carrier (p k)) r) := by
      rw [shrink_volumeMeasure_ball, Equiv.symm_apply_apply]
      exact hk.trans htransfer
    have hhaus := small_hausdorff_volume_lower_bound (C k).shrink
      ((F k).shrink.metric (-δ))
      (((F k).shrink.metric (-δ)).ball (equivShrink (C k).carrier (p k)) r) hsmall
    have heq : ν / ((c : ℝ) * r ^ (m + 1)) * r ^ (m + 1) = ν / (c : ℝ) := by
      field_simp
    dsimp only [S, smallBufferedCylinderSequence, BasedFlow.zeroBallVolume,
      bufferedCylinderSequence, BasedFlow.zeroBall, FlowCarrier.metricBall, RicciFlow.translate]
    rw [zero_add, heq]
    exact hhaus
  refine ⟨{
    time_bounds := ⟨hatime, hδ⟩
    sequence := S
    volume_compatibility := ?_
    zero_time_ball_compact := ?_
    spacetime_control := ?_
    all_time_curvature_control := ?_
    noncollapsing := hnoncollapse }, rfl⟩
  · intro k
    change (C k).shrink.metricHausdorffVolume ((F k).shrink.metric (-δ)) =
      (C k).shrink.metricHausdorffVolume ((F k).shrink.metric (0 + -δ))
    rw [zero_add]
  · intro A _
    exact Eventually.of_forall (fun k =>
      ((F k).shrink.metric (0 + -δ)).isCompact_closure_ball_of_metricComplete
        (by simpa only [zero_add, shrink_metricComplete_iff] using hcomplete k (-δ) hzero)
        (equivShrink (C k).carrier (p k)) A)
  · intro A _ I _ _ _ hI
    refine ⟨((m + 1 : ℕ) : ℝ) ^ 2 * 4, by positivity, ?_⟩
    filter_upwards [hcurv A] with k hk
    refine ⟨SmoothSpacetimeEmbedding.refl (S.flow k)
      (I ×ˢ (S.flow k).zeroBall A), fun _ _ => rfl, ?_⟩
    exact ⟨by positivity, fun t ht x hx => hk 0 ⟨hatime, hδ⟩ t (hI ht) x hx⟩
  · intro A _
    exact ⟨((m + 1 : ℕ) : ℝ) ^ 2 * 4, by positivity, hcurv A⟩




theorem exists_nonflat_pointed_limit_of_small_terminal_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) {a ν : ℝ} (ha : a ≤ -2)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc a 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc a 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hscalar : ∀ k, ∀ t ∈ Icc a 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : PointedGeometricConvergence
        (smallBufferedCylinderSequence C J F p a δ (by linarith) hJ),
        (∀ t ∈ Ioo (a + δ) δ,
          G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) ∧
        0 < (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base ∧
        ∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤
            ((m + 1 : ℕ) : ℝ) ^ 2 * 4 := by
  obtain ⟨ε, hε, hεone, hbuffer⟩ := exists_terminal_scalar_positive_time_buffer hC hm
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδone : δ < 1 := by dsimp only [δ]; linarith
  have hatime : a + δ < 0 := by linarith
  let S := smallBufferedCylinderSequence C J F p a δ (by linarith) hJ
  obtain ⟨H, hHS⟩ := exists_pointedCompactnessHypotheses_of_small_terminal_cylinders
    hC hm C J F p (by linarith : a ≤ -1) hδ hδone.le hatime hJ hcomplete hoperator
    L hL hscalar hν hvolume
  obtain ⟨P⟩ := pointedRicciFlowCompactness_of_local_derivative_estimates H
    hC.local_derivative_estimates_small
  have hlimit : ∃ G : PointedGeometricConvergence S,
      ∀ t ∈ Ioo (a + δ) δ,
        G.limitCarrier.metricComplete (G.limitFlow.metricAt t) := by
    rcases H with ⟨hT, seq, hvol, hcompact, hspace, hall, hnoncollapse⟩
    dsimp only at hHS
    subst seq
    exact ⟨P.geometric_limit, P.complete_interior⟩
  obtain ⟨G, hGcomplete⟩ := hlimit
  refine ⟨δ, hδ, hδone, G, hGcomplete, ?_, ?_⟩
  · apply G.curvatureTensorNorm_base_pos_of_scalar_lower_bound
      ⟨hatime, hδ⟩ (by norm_num : 0 < (1 : ℝ) / 2)
    filter_upwards [hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hk
    have hsub : Icc (-2 : ℝ) 0 ⊆ Icc a 0 := Icc_subset_Icc ha le_rfl
    have h := hbuffer (C k).carrier (J k) (F k)
      (fun _ ht => hJ k (hsub ht)) (fun t ht => hcomplete k t (hsub ht))
      (fun t ht => hoperator k t (hsub ht)) (p k)
      (fun t ht x hx => hscalar k t (hsub ht) x
        (hx.trans_le (ENNReal.ofReal_le_ofReal hk))) (hnormalize k)
      (-δ) ⟨by dsimp only [δ]; linarith, by linarith⟩
    change (1 : ℝ) / 2 ≤ ((F k).shrink.connection (0 + -δ)).scalarCurvature
      (equivShrink (C k).carrier (p k))
    rw [shrink_scalarCurvature, Equiv.symm_apply_apply, zero_add]
    exact h
  · apply G.curvatureTensorNorm_le_of_uniform_ball_bound ⟨hatime, hδ⟩
    intro A _
    filter_upwards [hL.eventually_ge_atTop A] with k hk
    intro t ht x hx
    have hshift : t - δ ∈ Icc a 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    change ((F k).shrink.connection (t - δ)).curvatureTensorNorm x ≤ _
    rw [shrink_curvatureTensorNorm]
    apply (F k).curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder hC
      (hJ k) (hoperator k) (p k) (hscalar k) hshift hshift hk
    change ((F k).shrink.metric (t - δ)).edist
      (equivShrink (C k).carrier (p k)) x < ENNReal.ofReal A at hx
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, shrink_edist,
      Equiv.symm_apply_apply] using hx

end RicciFlow

end PoincareConjecture
