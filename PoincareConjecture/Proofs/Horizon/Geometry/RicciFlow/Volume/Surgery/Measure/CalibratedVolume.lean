import PoincareConjecture.Proofs.M49.CalibratedVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.LocalFiniteness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.CalibratedTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.Basic




















set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SurgeryVolume


theorem sliceVolume_lt_top (F : SurgeryFlowData.{u}) {t : ℝ}
    (ht : t ∈ F.time_domain) : calibratedMetricVolume (F.metric t) univ < ⊤ :=
  calibratedMetricVolume_lt_top_of_isCompact (F.metric t) (F.slices_compact t ht)


theorem initialVolume_ne_top (F : SurgeryFlowData.{u}) :
    calibratedMetricVolume (F.metric 0) univ ≠ ⊤ :=
  (sliceVolume_lt_top F F.zero_mem).ne

end PoincareConjecture.SurgeryVolume
