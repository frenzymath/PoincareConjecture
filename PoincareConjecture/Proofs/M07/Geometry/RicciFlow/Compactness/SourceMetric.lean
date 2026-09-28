import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.FlowCarrier

universe u

@[instance_reducible] noncomputable def metricSpaceOf {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    MetricSpace C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier
  EMetricSpace.toMetricSpace (fun x y => g.edist_ne_top x y)

@[simp] theorem dist_metricSpaceOf {n : ℕ} (C : FlowCarrier n) (g : C.metric)
    (x y : C.carrier) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : T3Space C.carrier := C.t3Space
    letI : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : C.carrier → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    letI : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier
    @dist C.carrier (metricSpaceOf C g).toPseudoMetricSpace.toDist x y =
      (g.edist x y).toReal := by rfl

theorem metricBall_eq_metricBallOf {n : ℕ} (C : FlowCarrier n) (g : C.metric)
    (x : C.carrier) (r : ℝ) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : T3Space C.carrier := C.t3Space
    letI : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : C.carrier → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    letI : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier
    @Metric.ball C.carrier (metricSpaceOf C g).toPseudoMetricSpace x r =
      C.metricBall g x r := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier
  letI : MetricSpace C.carrier := metricSpaceOf C g
  ext y
  change dist y x < r ↔ EDist.edist x y < ENNReal.ofReal r
  rw [dist_comm, dist_metricSpaceOf,
    show EDist.edist x y = g.edist x y from rfl,
    ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top x y)]

end PoincareConjecture.FlowCarrier
