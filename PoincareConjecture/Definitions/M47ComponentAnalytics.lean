import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import PoincareConjecture.Definitions.M45ModelAnalytics

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

structure M47ComponentAnalyticBounds (C : ℝ) where
  duration : ℝ
  duration_pos : 0 < duration
  duration_le_one : duration ≤ 1
  curvature_threshold : ℝ
  one_le_curvature_threshold : 1 ≤ curvature_threshold
  constant : ℝ
  constant_pos : 0 < constant
  delta : StandardInitialMetric → MetricSurgeryConstants → ℝ
  delta_pos : ∀ g₀ K, 0 < delta g₀ K
  estimate :
    ∀ (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants)
      (F : SurgeryFlowData.{u}),
      F.standard_initial = g₀ → F.local_constants = K →
      F.parameters.C = C → F.parameters.epsilon ≤ 1 / 200 →
      ∀ t Q : ℝ, ∀ x : (F.slice t).carrier,
        (F.connection t).scalarCurvature x = Q → curvature_threshold ≤ Q →
        Set.Icc (t - duration / Q) t ⊆ F.time_domain →
        (∀ s ∈ Set.Icc (t - duration / Q) t,
          SurgeryPinchedAt (F.connection s) s) →
        (∀ s ∈ Set.Ico (t - duration / Q) t, ∀ y : (F.slice s).carrier,
          Q ≤ (F.connection s).scalarCurvature y →
            SurgeryCanonicalControl F s y F.parameters.epsilon C) →
        (∀ T ∈ Set.Icc (t - duration / Q) t, T ∈ F.surgery_times →
          F.parameters.delta T ≤ delta g₀ K) →
        ∀ N : SingularCComponent (F.metric t) (F.connection t) (2 * C),
          x ∈ N.carrier →
          M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x constant

end PoincareConjecture
