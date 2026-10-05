import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Provider

/-!
Adapted from Mapher `PoincareMT/Statements/M15Noncollapsing.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators intervalIntegral

universe u

namespace PoincareMT

structure GeneralizedNoncollapsingConclusion (n : ℕ) : Prop where
  uniform : M15GeneralizedUniformTheorem.{u} n
  provider_bridge :
    ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval)
      (G : GeneralizedLGeometryTransport n X time I)
      (Omega : Set G.Point)
      (taubar l₀ V r₀ : ℝ)
      (U : M15GeneralizedUniformData.{u} n taubar l₀ V),
      M15ProviderImpliesNoncollapse G Omega taubar l₀ V r₀ U.kappa U

end PoincareMT
