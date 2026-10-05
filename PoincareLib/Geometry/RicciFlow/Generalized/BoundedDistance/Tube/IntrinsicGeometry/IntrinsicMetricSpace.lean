import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicOpenMetric

/-!
# The actual finite intrinsic metric of the recut

The finite intrinsic diameter proved for the retained recut lets its open
Riemannian metric define a metric space with the original topology. This
is the metric used for completion and compactly confined rays, without
any completeness assertion. Source: Morgan--Tian Claims 10.13-10.14 and
Lemma 10.16, pp. 256-258; M28 derivation 134.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Finite original-region distances give a metric space on the literal
open subtype, with the topology inherited from the ambient manifold. -/
@[instance_reducible] noncomputable def intrinsicOpenMetricSpace
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    MetricSpace U := by
  let gU := intrinsicOpenMetric g U
  let : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 3) U
  apply EMetricSpace.toMetricSpace
  intro p q
  change gU.edist p q ≠ ⊤
  rw [intrinsicOpenMetric_edist]
  exact hfinite p q

/-- The construction preserves the original open-subtype topology literally. -/
theorem intrinsicOpenMetricSpace_topology
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    let d := intrinsicOpenMetricSpace g U hfinite
    (inferInstance : TopologicalSpace U) =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  rfl

/-- Extended distance is exactly the infimum over the original recut's
C1 competitors, with no ambient-distance substitution. -/
theorem intrinsicOpenMetricSpace_edist
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (p q : U) :
    letI := intrinsicOpenMetricSpace g U hfinite
    edist p q = intrinsicEDist g (U : Set M) (p : M) (q : M) :=
  intrinsicOpenMetric_edist g U p q

/-- Real distance is the finite real value of the same original-region
infimum used throughout the completion and ray arguments. -/
theorem intrinsicOpenMetricSpace_dist
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (p q : U) :
    letI := intrinsicOpenMetricSpace g U hfinite
    dist p q = (intrinsicEDist g (U : Set M) (p : M) (q : M)).toReal := by
  let := intrinsicOpenMetricSpace g U hfinite
  rw [dist_edist, intrinsicOpenMetricSpace_edist]

end PoincareMT.M28
