import PoincareConjecture.Proofs.M49.SlabVolume
import PoincareConjecture.Proofs.M49.CalibratedVolume
import PoincareConjecture.Proofs.M49.Mathlib.ExponentialLeftLimit









set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M49



theorem preEvent_exists_finite_left_limit (H : GeneralizedParabolicRescalingTheory.{u} 3)
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (hpinched : ∀ t ∈ Ico (F.event T hT).tMinus T, SurgeryPinchedAt (F.connection t) t) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      Tendsto (fun t => calibratedMetricVolume (F.metric t) univ)
        (𝓝[F.time_domain ∩ Iio T] T) (𝓝 L) := by
  have hstart : (F.event T hT).tMinus ∈ F.time_domain :=
    nonemptyEventPreInterval F T hT ⟨le_rfl, (F.event T hT).tMinus_lt⟩
  obtain ⟨L, hL, hlim⟩ := ENNReal.exists_finite_left_limit_of_exp_growth
    (F.event T hT).tMinus_lt (sliceVolume_lt_top F hstart).ne
    (fun s hs t ht hst => preEvent_volume_le_exp_mul H F T hT hpinched hs ht hst)
  exact ⟨L, hL, hlim.mono_left (nhdsWithin_mono _ inter_subset_right)⟩

end PoincareConjecture.M49
