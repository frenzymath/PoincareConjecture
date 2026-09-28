import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.WithinJetBoundsService
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.WithinFlowService
import PoincareConjecture.Proofs.M30.Mathlib.SpatialSliceJetService
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinFlowJetBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinBilinearFlow
import PoincareConjecture.Proofs.M28.Mathlib.SpatialJetsWithin









set_option autoImplicit false

universe uI uM uField uTime uSpace uValue uIndex

namespace PoincareConjecture.M30




theorem withinFlowJetBoundsService : WithinFlowJetBoundsService.{uI, uM} :=
  @RicciFlow.eventuallyBounded_within_pullbackCoefficients_of_spatial_bounds




theorem withinBilinearFlowService : WithinBilinearFlowService.{uM} :=
  @RicciFlow.exists_of_bilinear_within_spacetime_jets




theorem spatialSliceJetConvergenceService :
    SpatialSliceJetConvergenceService.{uField, uTime, uSpace, uValue, uIndex} :=
  @TendstoUniformlyOn.iteratedFDeriv_spatial_slice

end PoincareConjecture.M30
