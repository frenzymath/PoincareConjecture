import PoincareConjecture.Definitions.Ch09.NeckCapTopology









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g g' : RiemannianMetric 3 M}


noncomputable def ofMetricEq (h : g = g') (N : EpsilonNeck g) : EpsilonNeck g' :=
  h ▸ N


theorem ofMetricEq_data (h : g = g') (N : EpsilonNeck g) :
    (N.ofMetricEq h).epsilon = N.epsilon ∧
    (N.ofMetricEq h).center = N.center ∧
    (N.ofMetricEq h).coordinate_map = N.coordinate_map := by
  subst g'
  exact ⟨rfl, rfl, rfl⟩

end PoincareConjecture.EpsilonNeck
