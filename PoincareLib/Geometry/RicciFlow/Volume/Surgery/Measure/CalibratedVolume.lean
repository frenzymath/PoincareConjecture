import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.LocalFiniteness
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.CalibratedTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/CalibratedVolume.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Finite calibrated volume on compact slices

Morgan-Tian, Lemma 17.12, p. 410, uses finite volume of the compact
slices. The M10 coordinate formula for the actual calibrated Hausdorff
measure and continuity of its Gram density give local finiteness in every
dimension. See `proof-work/tasks/M49/derivations/01-foundations.md`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.SurgeryVolume

/-- Every included raw slice has finite volume (MT Lemma 17.12, p. 410). -/
theorem sliceVolume_lt_top (F : SurgeryFlowData.{u}) {t : ℝ}
    (ht : t ∈ F.time_domain) : calibratedMetricVolume (F.metric t) univ < ⊤ :=
  calibratedMetricVolume_lt_top_of_isCompact (F.metric t) (F.slices_compact t ht)

/-- The initial finite-volume field of the repaired Lemma 17.12, p. 410, data is automatic. -/
theorem initialVolume_ne_top (F : SurgeryFlowData.{u}) :
    calibratedMetricVolume (F.metric 0) univ ≠ ⊤ :=
  (sliceVolume_lt_top F F.zero_mem).ne

end PoincareMT.SurgeryVolume
