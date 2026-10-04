import PoincareLib.Geometry.Spacetime.Rescaling.Horizontal.Assembly
import PoincareLib.Geometry.Spacetime.Rescaling.ScaleBounds
import PoincareLib.Geometry.Spacetime.Rescaling.Domain.Calculus
import PoincareLib.Geometry.Spacetime.Rescaling.Domain.BallNeighborhoods
import PoincareLib.Geometry.Spacetime.Rescaling.Complete

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M13/Rescaling.lean`,
revision `0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See `references/ricci-flow/mapher/rescaling-import.json`. -/

/-!
# Assembly of the complete constructed spacetime rescaling

The geometry, horizontal calculus and both domain universes refer to the
same selected rescaled carrier and its unchanged interval system.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

open PoincareMT.Homothety

namespace PoincareMT.ParabolicRescaling

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

end PoincareMT.ParabolicRescaling
