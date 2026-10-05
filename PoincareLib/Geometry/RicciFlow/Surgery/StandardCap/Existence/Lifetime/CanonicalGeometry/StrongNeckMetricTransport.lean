import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap

/-!
# Equality transport of the actual terminal neck

Transport across the retained terminal metric equality preserves the
neck's actual epsilon, center and total coordinate. Source: Morgan-Tian
Theorem 12.28, pp. 323-324; M27 ancient-neck adapter derivation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g g' : RiemannianMetric 3 M}

/-- Transport the complete neck only along equality of its actual metric. -/
noncomputable def ofMetricEq (h : g = g') (N : EpsilonNeck g) : EpsilonNeck g' :=
  h ▸ N

/-- Equality transport keeps the requested geometric data literally. -/
theorem ofMetricEq_data (h : g = g') (N : EpsilonNeck g) :
    (N.ofMetricEq h).epsilon = N.epsilon ∧
    (N.ofMetricEq h).center = N.center ∧
    (N.ofMetricEq h).coordinate_map = N.coordinate_map := by
  subst g'
  exact ⟨rfl, rfl, rfl⟩

end PoincareMT.EpsilonNeck
