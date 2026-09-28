import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

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

theorem intrinsicOpenMetricSpace_topology
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    let d := intrinsicOpenMetricSpace g U hfinite
    (inferInstance : TopologicalSpace U) =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  rfl

theorem intrinsicOpenMetricSpace_edist
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (p q : U) :
    letI := intrinsicOpenMetricSpace g U hfinite
    edist p q = intrinsicEDist g (U : Set M) (p : M) (q : M) :=
  intrinsicOpenMetric_edist g U p q

theorem intrinsicOpenMetricSpace_dist
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (p q : U) :
    letI := intrinsicOpenMetricSpace g U hfinite
    dist p q = (intrinsicEDist g (U : Set M) (p : M) (q : M)).toReal := by
  let := intrinsicOpenMetricSpace g U hfinite
  rw [dist_edist, intrinsicOpenMetricSpace_edist]

end PoincareConjecture.M28
