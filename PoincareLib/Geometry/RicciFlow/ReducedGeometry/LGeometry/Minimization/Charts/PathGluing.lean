import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Gluing

/-! Reuse the dimension-independent variational declarations adapted from Mapher
`PoincareMT/Proofs/M08/PathGluing.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variational
  (exists_smooth_fin_gluing
    mem_fin_partition
    integrable_sum_fin_partition)

end PoincareMT.LGeometry
