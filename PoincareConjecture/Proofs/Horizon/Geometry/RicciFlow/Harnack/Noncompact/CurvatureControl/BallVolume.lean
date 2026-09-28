import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in
private lemma isOpen_metric_ball (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    IsOpen (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have heq : g.ball p r = Metric.eball p (ENNReal.ofReal r) := by
    ext x
    change g.edist p x < ENNReal.ofReal r ↔ edist x p < ENNReal.ofReal r
    rw [edist_comm]
    rfl
  rw [heq]
  exact Metric.isOpen_eball

private lemma volumeMeasure_ball_ne_top (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (r : ℝ) :
    g.volumeMeasure (g.ball p r) ≠ ⊤ := by
  have hs : g.ball p r ⊆ {q | g.edist p q ≤ ENNReal.ofReal r} := by
    intro q hq
    exact (show g.edist p q < ENNReal.ofReal r from hq).le
  exact (lt_of_le_of_lt (measure_mono hs)
    (g.volumeMeasure_lt_top_of_isCompact
      (g.isCompact_closedBall_of_metricComplete hc p r))).ne



theorem RicciFlow.ball_volume_lower_bound_of_integral_scalarCurvature_le
    {J : Set ℝ} (F : RicciFlow n M J) {a b P : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ interior J)
    (hD : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (p : M) (r : ℝ)
    (hP : ∀ t ∈ Ioo a b,
      (∫ y in (F.metric t).ball p r, (F.connection t).scalarCurvature y
        ∂(F.metric t).volumeMeasure) ≤ P) :
    ((F.metric a).volumeMeasure ((F.metric a).ball p r)).toReal - P * (b - a) ≤
      ((F.metric b).volumeMeasure ((F.metric b).ball p r)).toReal := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hball (t : ℝ) (ht : t ∈ Icc a b) :
      (F.metric a).ball p r ⊆ (F.metric t).ball p r :=
    F.ball_subset_ball_of_ricci_nonneg hJ p r ha ht ht.1
      (fun s hs x _ v => hRic s hs x v)
  have hR (t : ℝ) (ht : t ∈ Icc a b) (x : M) :
      0 ≤ (F.connection t).scalarCurvature x :=
    Finset.sum_nonneg (fun i _ => hRic t ht x _)
  have hfixed := F.volumeMeasure_lower_bound_of_integral_scalarCurvature_le hab hJ hD
    (isOpen_metric_ball (F.metric a) p r).measurableSet
    ((F.metric a).isCompact_closedBall_of_metricComplete (hcomplete a ha) p r)
    (fun q hx => (show (F.metric a).edist p q < ENNReal.ofReal r from hx).le)
    (P := P) (by
      intro t ht
      have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
      have hi : IntegrableOn (F.connection t).scalarCurvature
          ((F.metric t).ball p r) (F.metric t).volumeMeasure :=
        ((hD t ht').contMDiff_scalarCurvature.continuous.continuousOn.integrableOn_compact
        ((F.metric t).isCompact_closedBall_of_metricComplete (hcomplete t ht') p r)).mono_set
          (show (F.metric t).ball p r ⊆
            {q | (F.metric t).edist p q ≤ ENNReal.ofReal r} from
              fun q hx => (show (F.metric t).edist p q < ENNReal.ofReal r from hx).le)
      exact (setIntegral_mono_set hi (Eventually.of_forall (hR t ht'))
        (hball t ht').eventuallyLE).trans (hP t ht))
  exact hfixed.trans (ENNReal.toReal_mono
    (volumeMeasure_ball_ne_top (F.metric b) (hcomplete b hb) p r)
    (measure_mono (hball b hb)))



theorem RicciFlow.ball_volume_lower_bound_of_nonnegative_curvatureOperator
    {J : Set ℝ} (F : RicciFlow n M J) {a b P : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ interior J)
    (hD : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (p : M) (r : ℝ)
    (hP : ∀ t ∈ Ioo a b,
      (∫ y in (F.metric t).ball p r, (F.connection t).scalarCurvature y
        ∂(F.metric t).volumeMeasure) ≤ P) :
    ((F.metric a).volumeMeasure ((F.metric a).ball p r)).toReal - P * (b - a) ≤
      ((F.metric b).volumeMeasure ((F.metric b).ball p r)).toReal :=
  F.ball_volume_lower_bound_of_integral_scalarCurvature_le hab hJ hD hcomplete
    (fun t ht x v => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hD t ht) x (hoperator t ht x) v).1) p r hP

end PoincareConjecture
