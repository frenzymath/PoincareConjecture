import PoincareConjecture.Definitions.M34StandardCapExistence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedStandardCapUniquenessData
    (g₀ : StandardInitialMetric)
    (E : RepairedStandardCapExistenceData g₀) where
  lifetime_one : E.flow.base.lifetime = 1
  complete : ∀ t ∈ Set.Ico 0 E.flow.base.lifetime,
    MetricComplete (E.flow.metric t)
  unique_lifetime : ∀ G : MaximalStandardCapFlow g₀,
    E.flow.base.lifetime = G.base.lifetime
  unique_metric : ∀ G : MaximalStandardCapFlow g₀,
    ∀ t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.base.lifetime,
      E.flow.metric t = G.metric t

  partial_unique_metric : ∀ G : PartialStandardCapFlow g₀,
    ∀ t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.lifetime,
      E.flow.metric t = G.flow.metric t

  scalar_lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ t ∈ Set.Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      c / (1 - t) ≤ (E.flow.connection t).scalarCurvature x
  canonical : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        StandardCanonicalAlternative E.atlas E.flow t x epsilon C

end PoincareConjecture
