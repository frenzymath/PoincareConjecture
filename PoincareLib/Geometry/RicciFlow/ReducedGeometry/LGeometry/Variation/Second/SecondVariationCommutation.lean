import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationCoordinates
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Commutation

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/SecondVariationCommutation.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (coordinateCovariantU_congr
    coordinateCovariantU_contDiffOn
    coordinateCovariantS_contDiffOn
    coordinateCovariant_velocity_second)

end PoincareMT.LGeometry
