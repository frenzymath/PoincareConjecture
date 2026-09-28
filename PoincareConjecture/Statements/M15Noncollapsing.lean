import PoincareConjecture.Definitions.M15Noncollapsing
import PoincareConjecture.Statements.M14GeneralizedLGeometry
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture

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

structure CompactNoncollapsingConclusion : Prop where
  compact : M15CompactTheorem810.{u}

structure NoncollapsingConclusion (n : ℕ) : Prop where
  generalized : GeneralizedNoncollapsingConclusion.{u} n
  compact : CompactNoncollapsingConclusion.{u}

end PoincareConjecture
