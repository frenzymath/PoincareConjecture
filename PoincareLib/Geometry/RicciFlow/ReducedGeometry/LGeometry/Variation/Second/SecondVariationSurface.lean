import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationDensity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationCommutation
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Surface

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/SecondVariationSurface.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (curveCoordinateCovariantDerivative_congr
    curveCoordinateCovariantDerivative_sliceU
    curveCoordinateCovariantDerivative_sliceU_twice
    coordinateCurvature
    surfaceActionDensity
    surfaceActionDensity_second_hasDerivAt)

end PoincareMT.LGeometry
