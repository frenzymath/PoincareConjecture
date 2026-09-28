import PoincareConjecture.Statements.M13DomainTransport
import PoincareConjecture.Statements.M13BackwardEndpoints
import PoincareConjecture.Statements.M13ScaleBounds

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure GeneralizedParabolicRescaling {n : ℕ} {X : Type u} [TopologicalSpace X]
    {A : AdaptedMetricAtlas n X} (R : GeneralizedFlowCarrierConclusion A)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) where
  geometry : ParabolicSpacetimeRescaling R Q hQ a
  horizontal : ParabolicHorizontalCalculus geometry
  backwardEndpoints : ParabolicBackwardEndpointCalculus geometry
  bounds : ParabolicScaleBounds geometry
  domains : ParabolicDomainTransport.{u, u} geometry
  domain_calculus : ParabolicDomainCalculus domains
  coordinateDomains : ParabolicDomainTransport.{u, 0} geometry
  coordinate_domain_calculus : ParabolicDomainCalculus coordinateDomains
  ball_neighborhoods : ∀ (t : ℝ) (p : (R.slices t).Point) (r : ℝ), 0 < r →
    ∀ K : SpacetimeInterval, Nonempty (ParabolicBallNeighborhoodTransport geometry t p r K)

end PoincareConjecture
