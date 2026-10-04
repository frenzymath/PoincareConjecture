import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Extension.GlobalCurveExtension
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Extension.ChartExtensions
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Extension.Section

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/SmoothSectionExtension.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (restrictParametricSectionExtension
    gluedParametricSectionExtension
    exists_parametricSectionExtension_of_local
    exists_parametricSectionExtension)

end PoincareMT.LGeometry
