import PoincareConjecture.Statements.M15Noncollapsing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Proofs.M15

theorem provider_implies_noncollapse {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I) (Omega : Set G.Point)
    (taubar l₀ V r₀ : ℝ) (U : M15GeneralizedUniformData.{u} n taubar l₀ V) :
    M15ProviderImpliesNoncollapse G Omega taubar l₀ V r₀ U.kappa U := by
  intro provider
  refine ⟨rfl, ?_⟩
  intro p hp r hr hr₀ x hx K C _ _ _ _ _ B
  obtain ⟨E, ⟨D⟩⟩ := provider.provide p hp r hr hr₀ x hx K C B
  exact U.estimate X time I G (G.spacetime.timeFunction p) x E r K C B D

end PoincareConjecture.Proofs.M15
