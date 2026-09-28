import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier



set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace FlowCarrier



noncomputable def metricEMetricSpace {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    EMetricSpace C.carrier :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  EMetricSpace.ofRiemannianMetric (𝓡 n) C.carrier

theorem preconnected_metricEMetricSpace {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    @PreconnectedSpace C.carrier
      (C.metricEMetricSpace g).toUniformSpace.toTopologicalSpace := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  letI : EMetricSpace C.carrier := C.metricEMetricSpace g
  change @PreconnectedSpace C.carrier C.topologicalSpace
  exact ⟨C.connected.isPreconnected⟩

end FlowCarrier

end PoincareConjecture
