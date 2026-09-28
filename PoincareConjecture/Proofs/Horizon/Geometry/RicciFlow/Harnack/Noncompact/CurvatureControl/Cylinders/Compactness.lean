import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.VolumeTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.LocalControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Volume












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



noncomputable def bufferedCylinderSequence
    {n : ℕ} (C : ℕ → FlowCarrier.{0} n) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow n (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (a δ : ℝ) (ha : a < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k)) : PointedFlowSequence n (a + δ) δ where
  carrier := C
  flow k :=
    { base := p k
      flow := (F k).translate (-δ)
        (by
          rintro _ ⟨t, ht, rfl⟩
          exact interior_subset (hJ k ⟨by linarith [ht.1], by linarith [ht.2]⟩))
        ordConnected_Ioo (by
          refine ⟨a / 2 + δ, ⟨by linarith, by linarith⟩,
            a / 4 + δ, ⟨by linarith, by linarith⟩, ?_⟩
          linarith)
      volumeMeasure := (C k).metricHausdorffVolume ((F k).metric (-δ))
      spacetimeVectorField := fun _ _ => (1, 0)
      spacetimeVectorField_time := fun _ _ => rfl
      spacetimeVectorField_spatial_zero := fun _ _ => rfl }

@[simp] theorem bufferedCylinderSequence_metric
    {n : ℕ} (C : ℕ → FlowCarrier.{0} n) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow n (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (a δ : ℝ) (ha : a < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k)) (k : ℕ) (t : ℝ) :
    ((bufferedCylinderSequence C J F p a δ ha hJ).flow k).flow.metric t =
      (F k).metric (t - δ) := rfl

@[simp] theorem bufferedCylinderSequence_connection
    {n : ℕ} (C : ℕ → FlowCarrier.{0} n) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow n (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (a δ : ℝ) (ha : a < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k)) (k : ℕ) (t : ℝ) :
    ((bufferedCylinderSequence C J F p a δ ha hJ).flow k).flow.connection t =
      (F k).connection (t - δ) := rfl

private theorem hausdorff_volume_lower_bound
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



theorem exists_pointedCompactnessHypotheses_of_terminal_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
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
      H.sequence = bufferedCylinderSequence C J F p a δ (by linarith) hJ := by
  let S := bufferedCylinderSequence C J F p a δ (by linarith) hJ
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
    exact (F k).curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder
      hC (hJ k) (hoperator k) (p k) (hscalar k) (hshift hs) (hshift ht) hk x hx
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
    have hhaus := hausdorff_volume_lower_bound (C k) ((F k).metric (-δ))
      (((F k).metric (-δ)).ball (p k) r) (hk.trans htransfer)
    have heq : ν / ((c : ℝ) * r ^ (m + 1)) * r ^ (m + 1) = ν / (c : ℝ) := by
      field_simp
    dsimp only [S, BasedFlow.zeroBallVolume, bufferedCylinderSequence,
      BasedFlow.zeroBall, FlowCarrier.metricBall, RicciFlow.translate]
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
    change (C k).metricHausdorffVolume ((F k).metric (-δ)) =
      (C k).metricHausdorffVolume ((F k).metric (0 + -δ))
    rw [zero_add]
  · intro A _
    exact Eventually.of_forall (fun k =>
      ((F k).metric (0 + -δ)).isCompact_closure_ball_of_metricComplete
        (by simpa only [zero_add] using hcomplete k (-δ) hzero) (p k) A)
  · intro A _ I _ _ _ hI
    refine ⟨((m + 1 : ℕ) : ℝ) ^ 2 * 4, by positivity, ?_⟩
    filter_upwards [hcurv A] with k hk
    refine ⟨SmoothSpacetimeEmbedding.refl (S.flow k)
      (I ×ˢ (S.flow k).zeroBall A), fun _ _ => rfl, ?_⟩
    exact ⟨by positivity, fun t ht x hx => hk 0 ⟨hatime, hδ⟩ t (hI ht) x hx⟩
  · intro A _
    exact ⟨((m + 1 : ℕ) : ℝ) ^ 2 * 4, by positivity, hcurv A⟩

end PoincareConjecture.RicciFlow
