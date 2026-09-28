import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Selection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Volume.Normalization

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle ENNReal
universe u
namespace PoincareConjecture.RicciFlow
attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t3Space FlowCarrier.secondCountable
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

theorem exists_positive_volume_ancient_limit_of_unbounded_time_scalar
    {m : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M J) {a b ν : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hν : 0 < ν)
    (hvolume : ∀ t ∈ Icc a b, ∀ x : M,
      ENNReal.ofReal ν ≤ (F.metric t).volumeMeasure ((F.metric t).ball x 1))
    (hbad : ∀ K : ℝ, ∃ t ∈ Ioc a b, ∃ x : M,
      K < (t - a) * (F.connection t).scalarCurvature x) :
    ∃ (C : FlowCarrier.{0} (m + 1)) (δ : ℝ), 0 < δ ∧ δ < 1 ∧
      ∃ G : RicciFlow (m + 1) C.carrier (Iio δ), ∃ p : C.carrier,
        (∀ t ∈ Iio δ, MetricComplete (G.metric t)) ∧
        0 < (G.connection 0).curvatureTensorNorm p ∧
        (∀ t ∈ Iio δ, ∀ x : C.carrier,
          (G.connection t).curvatureTensorNorm x ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
        (∀ t ∈ Iio δ, ∀ x : C.carrier,
          (G.connection t).NonnegativeCurvatureOperator x) ∧
        (∀ r : ℝ, 0 < r →
          ENNReal.ofReal (((ν / 2 ^ (m + 1)) / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
            (G.metric 0).volumeMeasure ((G.metric 0).ball p r)) := by
  obtain ⟨p, τ, Q, A, hA, _, hQ, hsub, hτ, hnormalize, hscalar, hsmall⟩ :=
    F.exists_expanding_cylinders_of_unbounded_time_scalar hC hm hab hJ
      hcomplete hoperator hbad
  have hν' : 0 < ν / 2 ^ (m + 1) := by positivity
  have hlower (r : ℝ) (hr : 0 < r) : ∀ᶠ k in atTop,
      ENNReal.ofReal ((ν / 2 ^ (m + 1)) *
        (r / Real.sqrt (Q k)) ^ (m + 1)) ≤
          (F.metric (τ k)).volumeMeasure
            ((F.metric (τ k)).ball (p k) (r / Real.sqrt (Q k))) := by
    filter_upwards [hsmall r hr] with k hk
    apply (F.metric (τ k)).volume_lower_bound_of_center_in_half_ball
      (F.connection (τ k)) (by omega) (hcomplete _ (hτ k))
      (fun x v => ((F.connection (τ k)).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus _ M _ _) x (hoperator _ (hτ k) x) v).1)
      (p k) (p k) zero_lt_one (div_pos hr (Real.sqrt_pos.mpr (hQ k))) hk hν.le
    · let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
        ⟨(F.metric (τ k)).toRiemannianMetric⟩
      change (F.metric (τ k)).edist (p k) (p k) < ENNReal.ofReal (1 / 2)
      have hself : (F.metric (τ k)).edist (p k) (p k) = 0 :=
        Manifold.riemannianEDist_self
      rw [hself]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    · simpa only [one_pow, mul_one] using hvolume (τ k) (hτ k) (p k)
  obtain ⟨σ, _, δ, hδ, hδone, G, hc, hnonflat, hv⟩ :=
    exists_positive_volume_ancient_limit_of_rescaled_expanding_cylinders_components
      hC hm (fun _ => M) (fun _ => J) (fun _ => F) p Q τ A A hQ hA hA
      (fun k => (hsub k).trans hJ)
      (fun k t ht => hcomplete t (hsub k ht))
      (fun k t ht => hoperator t (hsub k ht)) hscalar hnormalize hν'
      (fun r hr => (hlower r hr).frequently)
  exact ⟨G.limitCarrier, δ, hδ, hδone, G.limitFlow, G.base,
    hc, hnonflat.1, hnonflat.2.1, hnonflat.2.2, hv⟩

end PoincareConjecture.RicciFlow
