import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ParameterIntegral

/-! Reuse the dimension-independent variation declarations adapted from Mapher
`PoincareMT/Proofs/M08/VariationIntegral.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (variationParameterDeriv
    variationParameterDeriv_contDiffOn
    hasDerivAt_variationParameter
    hasDerivAt_variationIntegral
    hasDerivAt_deriv_variationIntegral)

end PoincareMT.LGeometry
