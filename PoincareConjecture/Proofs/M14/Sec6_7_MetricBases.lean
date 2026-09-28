import PoincareConjecture.Definitions.M14MeasureTransport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

theorem exists_orthonormal_tangentBasis {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) :
    ∃ b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) p),
      ∀ i j, g.inner p (b i) (b j) = if i = j then 1 else 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  let b := (g.orthonormalBasis p).reindex (finCongr hdim)
  exact ⟨b.toBasis, fun i j => b.inner_eq_ite i j⟩

theorem exists_orthonormal_horizontalBasis {n : ℕ} {X : Type u}
    [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I) (x : G.Point) :
    ∃ b : Module.Basis (Fin n) ℝ (G.Horizontal x),
      ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
        if i = j then 1 else 0 := by
  let S := G.slices (G.spacetime.timeFunction x)
  let q : S.Point := ⟨x, rfl⟩
  obtain ⟨b, hb⟩ := exists_orthonormal_tangentBasis S.metricOnPoints q
  refine ⟨b.map (S.tangentEquiv q).toLinearEquiv, ?_⟩
  intro i j
  change G.spacetime.horizontalMetric.inner q.val
    (S.tangentEquiv q (b i)) (S.tangentEquiv q (b j)) = _
  rw [← S.metric_eq q]
  exact hb i j

end PoincareConjecture.M14
