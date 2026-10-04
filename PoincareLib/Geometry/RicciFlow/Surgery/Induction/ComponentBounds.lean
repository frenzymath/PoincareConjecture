import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Control.ModelBounds

/-!
Adapted from Mapher `PoincareMT/Definitions/M47ComponentAnalytics.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M47 analytic bounds from an actual compact-component history

The duration and analytic coefficient precede the standard model and flow.
The raw history is constructed inside the supporting theorem, using the
given pinching, earlier canonical neighborhoods and actual surgery data.
See `reviews/contracts/2026-09-15-m47-component-analytics-round1.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Uniform analytic output for the terminal weak-2C component branch.
There is no analytic, volume, noncollapse or ordinary-history premise. -/
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

end PoincareMT
