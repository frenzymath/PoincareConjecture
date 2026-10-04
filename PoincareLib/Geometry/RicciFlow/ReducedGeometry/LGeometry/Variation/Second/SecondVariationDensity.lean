import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Density

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/SecondVariationDensity.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (curveCoordinateCovariantDerivative
    curveCoordinateCovariantDerivative_contDiffOn
    chart_density_first_covariant_hasDerivAt
    chart_density_second_covariant_hasDerivAt)

end PoincareMT.LGeometry
