import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M08

open Set

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]

private theorem edist_ne_top_of_connected'
    {X : Type*} [PseudoEMetricSpace X] [ConnectedSpace X] :
    ∀ x y : X, edist x y ≠ ⊤ := by
  intro x y hxy
  let U : Set X := Metric.eball x ⊤
  have hUopen : IsOpen U := by
    exact Metric.isOpen_eball
  have hUclosed : IsClosed U := by
    exact Metric.isClosed_eball_top
  have hxU : x ∈ U := by
    exact Metric.mem_eball_self ENNReal.zero_lt_top
  have hUall : U = Set.univ :=
    IsClopen.eq_univ ⟨hUclosed, hUopen⟩ ⟨x, hxU⟩
  have hyU : y ∈ U := by
    rw [hUall]
    exact mem_univ y
  exact (ne_of_lt (Metric.mem_eball'.mp hyU)) hxy

theorem finiteEdistMetric (g : RiemannianMetric n M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    ∀ x y : M, edist x y ≠ ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact edist_ne_top_of_connected'

theorem existsLocalCompactMetricBall (g : RiemannianMetric n M) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    letI : PseudoMetricSpace M :=
      PseudoEMetricSpace.toPseudoMetricSpace (finiteEdistMetric g)
    ∃ r : ℝ, 0 < r ∧ IsCompact (Metric.closedBall x r) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  letI : PseudoMetricSpace M :=
    PseudoEMetricSpace.toPseudoMetricSpace (finiteEdistMetric g)
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  exact Metric.exists_isCompact_closedBall x

end PoincareConjecture.M08
