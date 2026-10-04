import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Regularity.EulerMomentum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Coordinates

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/VariationCoordinates.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (coordinateSlice_fst_hasDerivAt
    coordinateSlice_snd_hasDerivAt
    coordinate_mixed_hasDerivAt
    chart_density_hasDerivAt
    linear_moving_vector_hasDerivAt)

end PoincareMT.LGeometry

