import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationSurface
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Boundary

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/SecondVariationBoundary.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (surfaceAccelerationBoundaryPair
    surfaceAccelerationBoundaryPair_hasDerivAt
    surfaceActionDensity_second_boundary)

end PoincareMT.LGeometry
