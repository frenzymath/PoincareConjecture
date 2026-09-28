import PoincareConjecture.Statements.M49VolumeLoss
import PoincareConjecture.Proofs.M49.Lemma17_12_EventLoss
import PoincareConjecture.Proofs.M49.EventLossCertificate
import PoincareConjecture.Proofs.M49.DirectVolumeGrowth
import PoincareConjecture.Proofs.M49.UniformEventCount

set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture

theorem repairedVolumeLoss : RepairedVolumeLossTheory.{u} := by
  classical
  refine ⟨?_⟩
  intro g₀ K
  obtain ⟨c, hc, hcutoff⟩ := M49.exists_uniform_event_volume_loss.{u} g₀
  obtain ⟨d, hd, hdK, hcal⟩ := hcutoff K
  refine ⟨d, hd, hdK, ?_, ?_⟩
  · intro F C hstandard hconstants hdelta
    have hgeom := hcal
    rw [← hstandard, ← hconstants] at hgeom
    have hcert : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
        ∀ [Nonempty (F.slice T).carrier],
          ∃ D : RepairedSurgeryEventLossData F T hT,
            D.loss = if (F.event T hT).cap_count = 0 then 0 else
              ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) := by
      intro T hT hNonempty
      have hbound := hgeom F.parameters F.slice F.metric T (F.event T hT) (hdelta T hT)
      exact M49.exists_event_loss_certificate F T hT c hc
        (fun t ht => C.pinched t (M49.nonemptyEventPreInterval F T hT ht))
        (C.zero_cap_discard T hT) hbound.1 hbound.2
    let D : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
        ∀ [Nonempty (F.slice T).carrier], RepairedSurgeryEventLossData F T hT :=
      fun T hT _hNonempty => (hcert T hT).choose
    have hD (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
        (D T hT).loss = if (F.event T hT).cap_count = 0 then 0 else
          ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) :=
      (hcert T hT).choose_spec
    refine ⟨{
      initial_volume_ne_top := M49.initialVolume_ne_top F
      event_loss := D
      vanishing_volume := M49.vanishingVolumeData F
      volume_growth := fun a b ha hb hab =>
        M49.volume_growth_of_event_losses_direct F D ha hb hab
          (fun t ht => C.pinched t (F.time_domain_interval.out ha hb ht))
      loss_scale_factor := c
      loss_scale_factor_pos := hc
      horn_loss_lower_bound := ?_
      component_event_count_bound := ?_ }⟩
    · intro H hH
      have hhH := F.parameters.h_pos H hH
      refine ⟨c * (F.parameters.h H ^ 3 / d),
        mul_pos hc (div_pos (pow_pos hhH 3) hd), ?_⟩
      intro T hT hTI hNonempty hcap
      rw [hD, if_neg (Nat.ne_of_gt hcap)]
      refine ⟨ENNReal.ofReal_le_ofReal ?_, le_rfl⟩
      have hh := F.parameters.h_antitone hTI.1 hH hTI.2
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact div_le_div₀ (pow_nonneg (hhH.le.trans hh) 3)
        (pow_le_pow_left₀ hhH.le hh 3) (F.parameters.delta_pos T hTI.1) (hdelta T hT)
    · intro H hH
      obtain ⟨n, hn⟩ := M49.exists_uniform_event_prefix_bound
        c d H (calibratedMetricVolume (F.metric 0) univ) (F.parameters.h H)
        hc hd (M49.initialVolume_ne_top F) (F.parameters.h_pos H hH)
      refine ⟨n, ?_⟩
      intro S hS
      rcases S.eq_empty_or_nonempty with rfl | hne
      · exact Nat.zero_le _
      let b := S.max' hne
      have hbS : b ∈ S := S.max'_mem hne
      have hbT := (hS hbS).1.1
      have hbH : b ≤ H := (hS hbS).1.2.2
      have hb : b ∈ F.time_domain := F.surgery_times_subset hbT
      apply hn F b hb hbH
      · intro t ht
        exact C.pinched t (M49.initialInterval_subset F hb ht)
      · intro T hT _hTI hNonempty hzero
        obtain ⟨x, hx, _hvol⟩ := C.zero_cap_discard T hT hzero
        exact ⟨x, hx⟩
      · exact le_rfl
      · intro T hT
        exact ⟨hdelta T hT.1, F.parameters.h_antitone hT.2.1 hH (hT.2.2.trans hbH)⟩
      · intro T hT _hTI hNonempty
        exact (hgeom F.parameters F.slice F.metric T (F.event T hT) (hdelta T hT)).2
      · intro T hTS
        exact ⟨(hS hTS).1.1, (hS hTS).1.2.1, S.le_max' T hTS⟩
  · intro B V₀ hMin _hB hV₀ hhMin
    obtain ⟨n, hn⟩ := M49.exists_uniform_event_prefix_bound c d B V₀ hMin hc hd hV₀ hhMin
    refine ⟨n, ?_⟩
    intro F O hstandard hconstants hHB C hvol hscale S hS
    have hgeom := hcal
    rw [← hstandard, ← hconstants] at hgeom
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact Nat.zero_le _
    let b := S.max' hne
    have hbS : b ∈ S := S.max'_mem hne
    have hbT := (hS hbS).1
    have hbO : b ∈ Ico 0 O.H := (hS hbS).2
    have hb : b ∈ F.time_domain := F.surgery_times_subset hbT
    have hprefix : Icc 0 b ⊆ surgeryObservationInterval O :=
      fun t ht => ⟨ht.1, ht.2.trans_lt hbO.2⟩
    apply hn F b hb (hbO.2.le.trans hHB)
    · exact fun t ht => C.pinched t (hprefix ht)
    · intro T hT _hTI hNonempty hzero
      obtain ⟨x, hx, _hpositive⟩ := C.zero_cap_discard T hT hzero
      exact ⟨x, hx⟩
    · exact hvol
    · exact fun T hT => hscale T ⟨hT.1, hprefix hT.2⟩
    · intro T hT hTI hNonempty
      exact (hgeom F.parameters F.slice F.metric T (F.event T hT)
        (hscale T ⟨hT, hprefix hTI⟩).1).2
    · intro T hTS
      exact ⟨(hS hTS).1, (hS hTS).2.1, S.le_max' T hTS⟩

end PoincareConjecture
