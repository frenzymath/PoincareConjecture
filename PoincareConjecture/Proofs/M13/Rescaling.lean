import PoincareConjecture.Proofs.M13.HorizontalCalculus
import PoincareConjecture.Proofs.M13.ScaleBounds
import PoincareConjecture.Proofs.M13.DomainCalculus
import PoincareConjecture.Proofs.M13.BallNeighborhoods
import PoincareConjecture.Definitions.M13Rescaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X}

noncomputable def generalizedRescaling (hEquation : GeneralizedRicciGaugeTheory.{u} n)
    (R : GeneralizedFlowCarrierConclusion A) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    GeneralizedParabolicRescaling R Q hQ a where
  geometry := spacetimeRescaling R Q hQ a
  horizontal := parabolicHorizontalCalculus hEquation
  backwardEndpoints := parabolicBackwardEndpointCalculus (spacetimeRescaling R Q hQ a)
  bounds := parabolicScaleBounds (spacetimeRescaling R Q hQ a)
    (parabolicHorizontalCalculus hEquation)
  domains := domainTransport.{u, u} R Q hQ a
  domain_calculus := domainCalculus R.compatible
  coordinateDomains := domainTransport.{u, 0} R Q hQ a
  coordinate_domain_calculus := domainCalculus R.coordinate_compatible
  ball_neighborhoods := ballNeighborhoodTransport (domainTransport.{u, u} R Q hQ a)

end PoincareConjecture.M13
