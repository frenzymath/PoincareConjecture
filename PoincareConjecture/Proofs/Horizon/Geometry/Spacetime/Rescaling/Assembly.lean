import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Horizontal.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.ScaleBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.BallNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Complete










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

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

end PoincareConjecture.ParabolicRescaling
