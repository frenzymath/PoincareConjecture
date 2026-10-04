import PoincareLib.Geometry.RicciFlow.Blowup.DenseTime
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional

/-! Scoped source spelling for the current dense-time M29 service. -/

namespace PoincareMT.FinalSource

scoped macro "m29GeneralizedBoundedDistance" : term =>
  `(PoincareMT.DenseTime.generalizedBoundedDistance)

scoped macro "twoDimensionalClassificationTheory" : term =>
  `(PoincareMT.twoDimensionalAncientAndShrinkingSolitonClassification)

end PoincareMT.FinalSource
