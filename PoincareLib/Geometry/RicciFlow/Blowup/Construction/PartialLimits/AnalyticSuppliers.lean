import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.WithinJetBoundsService
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.WithinFlowService
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Analysis.SpatialSliceJetService
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Coordinates.WithinFlowJetBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Coordinates.WithinBilinearFlow
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.SpatialJetsWithin

/-!
# Included-time analytic suppliers

The M28 proofs supply the exact analytic obligations used by M30's
retained-flow assemblies. Every filter, domain and universe in those
interfaces is retained (Morgan--Tian Proposition 5.14, pp. 90--91).
-/

set_option autoImplicit false

universe uI uM uField uTime uSpace uValue uIndex

namespace PoincareMT.M30

/-- Actual flows supply mixed within-jet bounds, including the tested
closure points, from spatial bounds and positive ellipticity
(Morgan--Tian Proposition 5.14, pp. 90--91). -/
theorem withinFlowJetBoundsService : WithinFlowJetBoundsService.{uI, uM} :=
  @RicciFlow.eventuallyBounded_within_pullbackCoefficients_of_spatial_bounds

/-- Included-time bilinear jets realize the supplied total metric family
as an actual Ricci flow on the same domain
(Morgan--Tian Proposition 5.14, pp. 90--91). -/
theorem withinBilinearFlowService : WithinBilinearFlowService.{uM} :=
  @RicciFlow.exists_of_bilinear_within_spacetime_jets

/-- Spatial restriction of within jets retains the original tested set
and includes every time endpoint in that set
(Morgan--Tian Proposition 5.14, pp. 90--91). -/
theorem spatialSliceJetConvergenceService :
    SpatialSliceJetConvergenceService.{uField, uTime, uSpace, uValue, uIndex} :=
  @TendstoUniformlyOn.iteratedFDeriv_spatial_slice

end PoincareMT.M30
