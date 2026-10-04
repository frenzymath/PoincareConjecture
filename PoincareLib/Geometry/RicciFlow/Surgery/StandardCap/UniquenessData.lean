import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceData

/-!
Adapted from Mapher `PoincareMT/Definitions/M35StandardCapUniqueness.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M35 repaired standard-cap uniqueness and estimates

The data retains the actual M34 flow comparison, unit lifetime, completeness,
scalar lower rate, and time-dependent canonical alternatives.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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
  /-- Common-domain uniqueness for a raw partial standard flow. Maximality is
      not needed for this comparison; it is used only by `unique_lifetime`. -/
  partial_unique_metric : ∀ G : PartialStandardCapFlow g₀,
    ∀ t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.lifetime,
      E.flow.metric t = G.flow.metric t
  /-- Proposition 12.31, pp. 325-326: one positive coefficient bounds scalar
  curvature below by c/(1-t) on this actual standard flow throughout [0,1).
  See the corrected ODE argument in the 2026-09-15 scalar-rate contract. -/
  scalar_lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ t ∈ Set.Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      c / (1 - t) ≤ (E.flow.connection t).scalarCurvature x
  canonical : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        StandardCanonicalAlternative E.atlas E.flow t x epsilon C

end PoincareMT
