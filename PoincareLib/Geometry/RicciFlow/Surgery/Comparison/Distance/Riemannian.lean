import PoincareLib.Geometry.Riemannian.Connection
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Distance.ConnectedEMetric
/-!
# The actual Riemannian distance as a real metric

The coordinate smoothing estimates for Claim 18.22, Morgan-Tian p. 433,
use real distances. On a preconnected manifold the supplied Riemannian
extended distance is finite. Mathlib's metric conversion preserves both
that extended distance and the original topology definitionally.

The semantic argument is in the SurgeryComparison.Transport global-smoothing derivation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.SurgeryComparison.Transport

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

/-- Install the real metric of the specified Riemannian metric on a
preconnected manifold, with its original topology. This supplies the
metric convention in the smoothing step of Claim 18.22, p. 433. -/
@[instance_reducible]
noncomputable def metricSpaceOfRiemannianMetric (g : RiemannianMetric n M) :
    MetricSpace M := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

/-- The installed metric has literally the supplied extended distance;
no coordinate distance replaces it. Claim 18.22, Morgan-Tian p. 433. -/
theorem metricSpaceOfRiemannianMetric_edist (g : RiemannianMetric n M) (x y : M) :
    @edist M (metricSpaceOfRiemannianMetric g).toEDist x y = g.edist x y := rfl

/-- The metric conversion retains the original manifold topology;
Claim 18.22, Morgan-Tian p. 433. -/
theorem metricSpaceOfRiemannianMetric_topology (g : RiemannianMetric n M) :
    (metricSpaceOfRiemannianMetric g).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M) := rfl

end PoincareMT.SurgeryComparison.Transport
