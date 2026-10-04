import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartCover

/-! Reuse the dimension-independent variational declarations adapted from Mapher
`PoincareMT/Proofs/M08/ChartCover.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum
  (uniform_composition_on_compact_core
    exists_compact_partition_of_uniform_limit)

end PoincareMT.LGeometry
