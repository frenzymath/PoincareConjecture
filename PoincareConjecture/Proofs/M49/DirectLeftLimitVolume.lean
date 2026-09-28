import PoincareConjecture.Proofs.M49.DirectSlabVolume
import PoincareConjecture.Proofs.M49.CalibratedVolume
import PoincareConjecture.Proofs.M49.Mathlib.ExponentialLeftLimit
import PoincareConjecture.Proofs.M49.RegularLimitVolume

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M49

theorem preEvent_exists_finite_left_limit_direct
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
    (fun s hs t ht hst => preEvent_volume_le_exp_mul_direct F T hT hpinched hs ht hst)
  exact ⟨L, hL, hlim.mono_left (nhdsWithin_mono _ inter_subset_right)⟩

theorem event_regular_limit_volume_le_left_limit_direct
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] {L : ℝ≥0∞}
    (hlim : Tendsto (fun t => calibratedMetricVolume (F.metric t) univ)
      (𝓝[F.time_domain ∩ Iio T] T) (𝓝 L)) :
    calibratedMetricVolume (F.event T hT).limit_metric univ ≤ L := by
  let E := F.event T hT
  have hleft : 𝓝[<] T ≤ 𝓝[F.time_domain ∩ Iio T] T := by
    rw [← nhdsWithin_Ico_eq_nhdsLT E.tMinus_lt]
    apply nhdsWithin_mono
    exact fun _ ht => ⟨nonemptyEventPreInterval F T hT ht, ht.2⟩
  have heq : (fun t => calibratedMetricVolume (E.pre_flow.metric t) univ) =ᶠ[𝓝[<] T]
      (fun t => calibratedMetricVolume (F.metric t) univ) := by
    filter_upwards [Ioo_mem_nhdsLT E.tMinus_lt] with t ht
    let rt : Ico E.tMinus T := ⟨t, ⟨ht.1.le, ht.2⟩⟩
    apply (volume_univ_eq_of_metric_isometry_direct (E.pre_flow.metric t)
      (F.metric t) (E.pre_identify rt) _).symm
    intro x a b
    simpa only [one_mul] using E.pre_metric rt x a b
  have hfixed := (hlim.mono_left hleft).congr' heq.symm
  exact (event_regular_limit_volume_le_liminf E).trans_eq hfixed.liminf_eq

end PoincareConjecture.M49
