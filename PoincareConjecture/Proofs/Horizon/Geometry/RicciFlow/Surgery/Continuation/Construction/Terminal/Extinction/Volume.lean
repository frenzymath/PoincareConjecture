import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Evolution.DirectSlabVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.CalibratedVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Analysis.ExponentialLeftLimit

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.RepairedContinuationInput

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)

include I

theorem exists_finite_left_volume :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      Tendsto (fun t => calibratedMetricVolume (F.metric t) univ) (𝓝[<] T) (𝓝 L) := by
  apply ENNReal.exists_finite_left_limit_of_exp_growth (k := 6) I.last_slab.start_lt
    (SurgeryVolume.sliceVolume_lt_top F I.last_slab.start_mem).ne
  intro s hs t ht hst
  have hJ : Icc s t ⊆ F.time_domain := fun r hr =>
    I.last_slab.time_subset ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩
  have hfree : Disjoint F.surgery_times (Ioc s t) := by
    apply I.last_slab.surgery_free.mono_right
    intro r hr
    exact ⟨hs.1.trans_lt hr.1, hr.2.trans_lt ht.2⟩
  exact SurgeryVolume.regular_volume_le_exp_mul_direct F hst hJ hfree
    (fun r hr => I.pinched r (hJ hr))

end PoincareConjecture.RepairedContinuationInput
