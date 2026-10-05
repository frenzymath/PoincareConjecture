import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Extension.Pasting

/-! Reuse the dimension-independent variational declarations adapted from Mapher
`PoincareMT/Proofs/M08/SmoothEndpointPasting.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variational
  (contDiff_of_derivative_tower
    pasteEndpointDerivatives
    pasteEndpointDerivatives_eq_left
    pasteEndpointDerivatives_eq_middle
    pasteEndpointDerivatives_eq_right
    pasteEndpointDerivatives_hasDerivAt
    smooth_pasting_of_matching_endpoint_jets)

end PoincareMT.LGeometry
