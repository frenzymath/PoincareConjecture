import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Harnack.Basic

/-!
# The emetric space of a selected Riemannian metric

Morgan-Tian, Lemma 12.6, printed p. 297. These bridges expose the exact
metric structure already used by the frozen `MetricComplete` definition.
The distance and topology are identified separately so comparison proofs
can use those identities without repeatedly reducing the construction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

/-- The selected metric's emetric structure, as used in Lemma 12.6, p. 297. -/
@[instance_reducible]
noncomputable def toEMetricSpace (g : RiemannianMetric n M) : EMetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  EMetricSpace.ofRiemannianMetric (𝓡 n) M

/-- Lemma 12.6, p. 297, compares metrics whose induced topologies are the manifold topology. -/
theorem toEMetricSpace_topology (g : RiemannianMetric n M) :
    g.toEMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl

/-- The distance in Lemma 12.6, p. 297, is the actual selected metric's path distance. -/
theorem toEMetricSpace_edist (g : RiemannianMetric n M) (x y : M) :
    g.toEMetricSpace.edist x y = g.edist x y := rfl

/-- Unfold the frozen completeness predicate through its identical selected metric.
Used in Lemma 12.6, p. 297. -/
theorem metricComplete_iff_toEMetricSpace (g : RiemannianMetric n M) :
    MetricComplete g ↔ @CompleteSpace M g.toEMetricSpace.toUniformSpace := Iff.rfl

end PoincareMT.RiemannianMetric
