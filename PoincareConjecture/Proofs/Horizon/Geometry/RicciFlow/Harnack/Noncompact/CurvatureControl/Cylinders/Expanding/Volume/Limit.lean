import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.VolumeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Volume.Selection








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold



theorem exists_positive_volume_ancient_limit_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hfailure : ∀ r : ℝ, 0 < r → ∃ᶠ k in atTop, ENNReal.ofReal (ν * r ^ (m + 1)) ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence (fun k => (C (σ k)).shrink)
        (fun k t => (F (σ k)).shrink.metric (t - δ))
        (fun k => equivShrink (C (σ k)).carrier (p (σ k))) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) ∧
        (∀ r : ℝ, 0 < r → ENNReal.ofReal ((ν / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
          (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base r)) := by
  have hzero : ∀ᶠ k in atTop, (0 : ℝ) ∈ Icc (-A k) 0 := by
    filter_upwards [hA.eventually_ge_atTop 0] with k hk
    exact ⟨neg_nonpos.mpr hk, le_rfl⟩
  have hcomplete0 : ∀ᶠ k in atTop, MetricComplete ((F k).metric 0) :=
    hzero.mono (fun k hk => hcomplete k 0 hk)
  have hRic : ∀ᶠ k in atTop, ∀ x : (C k).carrier,
      ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ ((F k).connection 0).ricci x v v := by
    filter_upwards [hzero] with k hk x v
    exact (((F k).connection 0).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) _ _ _) x (hoperator k 0 hk x) v).1
  obtain ⟨σ, hσ, hvolume⟩ := RiemannianMetric.exists_subsequence_ball_volume_lower_bound_of_frequently
    (by omega : 1 ≤ m + 1) C (fun k => (F k).metric 0) (fun k => (F k).connection 0)
    hcomplete0 hRic p hν.le hfailure
  have hunit : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F (σ k)).metric 0).volumeMeasure (((F (σ k)).metric 0).ball (p (σ k)) 1) := by
    simpa only [one_pow, mul_one] using hvolume 1 (by norm_num)
  obtain ⟨δ, hδ, hδone, G, hGcomplete, hGcurvature⟩ :=
    exists_nonflat_ancient_limit_of_small_expanding_cylinders hC hm
      (fun k => C (σ k)) (fun k => J (σ k)) (fun k => F (σ k))
      (fun k => p (σ k)) (A ∘ σ) (L ∘ σ)
      (hA.comp hσ.tendsto_atTop) (hL.comp hσ.tendsto_atTop)
      (fun k => hJ (σ k)) (fun k => hcomplete (σ k))
      (fun k => hoperator (σ k)) (fun k => hscalar (σ k))
      (fun k => hnormalize (σ k)) hν hunit
  refine ⟨σ, hσ, δ, hδ, hδone, G, hGcomplete, hGcurvature, ?_⟩
  exact small_ancient_limit_ball_volume_lower_bound hC hm
    (fun k => C (σ k)) (fun k => J (σ k)) (fun k => F (σ k))
    (fun k => p (σ k)) (A ∘ σ) (L ∘ σ)
    (hA.comp hσ.tendsto_atTop) (hL.comp hσ.tendsto_atTop)
    (fun k => hJ (σ k)) (fun k => hcomplete (σ k))
    (fun k => hoperator (σ k)) (fun k => hscalar (σ k))
    hν.le hδ hδone.le hvolume G (hGcomplete 0 hδ)

end PoincareConjecture.RicciFlow
