import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.VariationCoordinates
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Coordinates

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/SecondVariationCoordinates.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (coordinatePartialS
    coordinatePartialU
    coordinatePartialS_contDiffOn
    coordinatePartialU_contDiffOn
    coordinatePartials_commute
    coordinateCovariantS
    coordinateCovariantU
    coordinateCovariant_torsion
    coordinateCovariant_commutator
    chart_pair_covariant_hasDerivAt
    chart_pair_moving_covariant_hasDerivAt)

end PoincareMT.LGeometry
