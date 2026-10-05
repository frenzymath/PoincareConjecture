import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Provider

/-!
# Noncollapsing from a configuration provider

Adapted from Mapher `Proofs/M15/Thm8_1_Provider.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`.
Morgan-Tian Theorem 8.1, p. 169.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.Generalized.Noncollapse

/-- Apply the uniform estimate to each configuration supplied on the region. -/
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

end PoincareMT.Generalized.Noncollapse
