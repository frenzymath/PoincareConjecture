import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.LimitLowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.TerminalMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Geometry















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric



theorem rescaled_ball_volume_lower_bound_of_asymptoticVolumeRatio
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p y : M) (hy : g.edist p y ≠ ⊤)
    (hvolume : 0 < g.asymptoticVolumeRatio p)
    (Q : ℝ) (hQ : 0 < Q) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((g.asymptoticVolumeRatio p / 2 ^ n) * r ^ n) ≤
      (rescaledMetric g Q hQ).volumeMeasure ((rescaledMetric g Q hQ).ball y r) := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hbase := g.ball_volume_lower_bound_of_asymptoticVolumeRatio D hn hc hRic
    p y hy hvolume.le (div_pos hr hsqrt) le_rfl
  rw [rescaledMetric_ball_allDimensions, rescaledMetric_volumeMeasure,
    Measure.smul_apply, smul_eq_mul]
  have hscale := mul_le_mul_right hbase (ENNReal.ofReal (Real.sqrt Q) ^ n)
  apply le_trans _ hscale
  rw [← ENNReal.ofReal_pow hsqrt.le,
    ← ENNReal.ofReal_mul (pow_nonneg hsqrt.le n)]
  apply le_of_eq
  congr 1
  rw [div_pow]
  field_simp

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



noncomputable def ancientRescaledPointedSequence
    {n : ℕ} {T' T : ℝ} (C : FlowCarrier n)
    (F : RicciFlow n C.carrier (Iic 0)) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (τ : ℕ → ℝ) (q : ℕ → C.carrier) (hT : T' < 0 ∧ 0 < T)
    (htime : ∀ k, MapsTo (fun s : ℝ => τ k + s / Q k) (Ioo T' T) (Iic 0)) :
    PointedFlowSequence n T' T where
  carrier := fun _ => C
  flow k :=
    { base := q k
      flow := F.parabolicRescale (Q k) (hQ k) (τ k) (htime k) ordConnected_Ioo (by
        refine ⟨0, hT, T / 2, ⟨by linarith [hT.1, hT.2], by linarith [hT.2]⟩, ?_⟩
        linarith [hT.2])
      volumeMeasure := C.metricHausdorffVolume (rescaledMetric (F.metric (τ k)) (Q k) (hQ k))
      spacetimeVectorField := fun _ _ => (1, 0)
      spacetimeVectorField_time := fun _ _ => rfl
      spacetimeVectorField_spatial_zero := fun _ _ => rfl }




theorem rescaled_limit_ball_volume_lower_bound_of_asymptoticVolumeRatio
    {n : ℕ} {T' T : ℝ} (C : FlowCarrier n)
    (hC : RicciFlowCurvatureTheory.{0}) (F : RicciFlow n C.carrier (Iic 0))
    (hn : 1 ≤ n) (t₀ : ℝ) (p : C.carrier)
    (hcomplete : MetricComplete (F.metric t₀))
    (hoperator : ∀ x, (F.connection t₀).NonnegativeCurvatureOperator x)
    (hvolume : 0 < (F.metric t₀).asymptoticVolumeRatio p)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (q : ℕ → C.carrier)
    (hT : T' < 0 ∧ 0 < T)
    (htime : ∀ k, MapsTo (fun s : ℝ => t₀ + s / Q k) (Ioo T' T) (Iic 0))
    (G : PointedGeometricConvergence
      (F.ancientRescaledPointedSequence C Q hQ (fun _ => t₀) q hT htime))
    (hlimitComplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0)) :
    ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (((F.metric t₀).asymptoticVolumeRatio p / 2 ^ n) * r ^ n) ≤
        G.limitCarrier.metricRiemannianVolume
          (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall r) := by
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  apply G.ball_volume_lower_bound_of_metricComplete_zero hT hlimitComplete
  intro r hr
  apply Eventually.of_forall
  intro k
  let j := G.subsequence k
  have hbound := (F.metric t₀).rescaled_ball_volume_lower_bound_of_asymptoticVolumeRatio
    (F.connection t₀) hn hcomplete
    (fun x v => ((F.connection t₀).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n C.carrier (F.metric t₀) (F.connection t₀)) x (hoperator x) v).1)
    p (q j) ((F.metric t₀).edist_ne_top p (q j)) hvolume (Q j) (hQ j) hr
  change ENNReal.ofReal (((F.metric t₀).asymptoticVolumeRatio p / 2 ^ n) * r ^ n) ≤
    (rescaledMetric (F.metric (t₀ + 0 / Q j)) (Q j) (hQ j)).volumeMeasure
      ((rescaledMetric (F.metric (t₀ + 0 / Q j)) (Q j) (hQ j)).ball (q j) r)
  simpa only [zero_div, add_zero] using hbound




theorem earlier_rescaled_limit_ball_volume_lower_bound_of_asymptoticVolumeRatio
    {m : ℕ} {T' T : ℝ} (C : FlowCarrier (m + 1))
    (hC : RicciFlowCurvatureTheory.{0}) (F : RicciFlow (m + 1) C.carrier (Iic 0))
    (hm : 0 < m) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : C.carrier)
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hvolume : 0 < (F.metric t₀).asymptoticVolumeRatio p)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (τ : ℕ → ℝ) (hτ : ∀ k, τ k ≤ t₀)
    (q : ℕ → C.carrier) (hT : T' < 0 ∧ 0 < T)
    (htime : ∀ k, MapsTo (fun s : ℝ => τ k + s / Q k) (Ioo T' T) (Iic 0))
    (G : PointedGeometricConvergence
      (F.ancientRescaledPointedSequence C Q hQ τ q hT htime))
    (hlimitComplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0)) :
    ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (((F.metric t₀).asymptoticVolumeRatio p / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
        G.limitCarrier.metricRiemannianVolume
          (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall r) := by
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  apply G.ball_volume_lower_bound_of_metricComplete_zero hT hlimitComplete
  intro r hr
  apply Eventually.of_forall
  intro k
  let j := G.subsequence k
  have hj0 : τ j ≤ 0 := (hτ j).trans ht₀
  have hratio : (F.metric t₀).asymptoticVolumeRatio p ≤
      (F.metric (τ j)).asymptoticVolumeRatio p :=
    F.antitoneOn_asymptoticVolumeRatio_of_bounded_ancient hC hm
      hcomplete hoperator hK hbound p hj0 ht₀ (hτ j)
  have hscaled := (F.metric (τ j)).rescaled_ball_volume_lower_bound_of_asymptoticVolumeRatio
    (F.connection (τ j)) (by omega) (hcomplete (τ j) hj0)
    (fun x v => ((F.connection (τ j)).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) C.carrier (F.metric (τ j)) (F.connection (τ j)))
      x (hoperator (τ j) hj0 x) v).1)
    p (q j) ((F.metric (τ j)).edist_ne_top p (q j)) (hvolume.trans_le hratio)
    (Q j) (hQ j) hr
  have hconstant := ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hratio (by positivity : (0 : ℝ) ≤ 2 ^ (m + 1)))
      (pow_nonneg hr.le (m + 1)))
  have hresult := hconstant.trans hscaled
  change ENNReal.ofReal (((F.metric t₀).asymptoticVolumeRatio p / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
    (rescaledMetric (F.metric (τ j + 0 / Q j)) (Q j) (hQ j)).volumeMeasure
      ((rescaledMetric (F.metric (τ j + 0 / Q j)) (Q j) (hQ j)).ball (q j) r)
  simpa only [zero_div, add_zero] using hresult

end PoincareConjecture.RicciFlow
