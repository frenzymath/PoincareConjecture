import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Event.EventHistory
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Analysis.ExponentialJumpBalance

/-!
Adapted from Mapher `PoincareMT/Proofs/M50/Lemma17_12_Telescoping.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Weighted losses for arbitrary finite event subsets

Morgan-Tian Lemma 17.12, p. 410, bounds selected surgery losses by the
initial volume. We apply M49's general finite-jump balance to the exact
supplied certificate, using only the maximum of the selected finite set.
See `reviews/contracts/2026-09-20-m50-finite-subsets.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal BigOperators

universe u

namespace PoincareMT.SurgeryFiniteness

/-- Constant losses below the actual selected event losses telescope
against initial volume (MT Lemma 17.12, p. 410). The whole surgery set
need not be finite, and no outside-domain horizon is evaluated. -/
theorem weighted_constant_losses_le_initial
    (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F)
    (V : RepairedVolumeLossData F C) (sigma : ℝ) (S : Finset ℝ)
    (hS : ∀ T ∈ S, ∃ hT : T ∈ F.surgery_times,
      ∃ hN : Nonempty (F.slice T).carrier,
        letI := hN
        ENNReal.ofReal sigma ≤ (V.event_loss T hT).loss) :
    ∑ T ∈ S, ENNReal.ofReal (Real.exp (-(6 * T))) * ENNReal.ofReal sigma ≤
      calibratedMetricVolume (F.metric 0) univ := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  let b := S.max' hne
  obtain ⟨hb, _hN, _hloss⟩ := hS b (S.max'_mem hne)
  have hb0 : 0 ≤ b := (SurgeryVolume.surgeryTime_pos F hb).le
  have hJ : Icc 0 b ⊆ F.time_domain :=
    SurgeryVolume.initialInterval_subset F (F.surgery_times_subset hb)
  have hSI : (S : Set ℝ) ⊆ Ioc 0 b := by
    intro T hTS
    obtain ⟨hT, _hN, _hloss⟩ := hS T hTS
    exact ⟨SurgeryVolume.surgeryTime_pos F hT, S.le_max' T hTS⟩
  have hbalance := ENNReal.expWeighted_add_sum_le_of_finite_left_jumps 6
    (V := fun t => calibratedMetricVolume (F.metric t) univ)
    (loss := fun _ => ENNReal.ofReal sigma) S hb0 hSI (by
      intro x hx y hy hxy _hdis
      exact V.volume_growth x y (hJ hx) (hJ hy) hxy) (by
      intro T hTS
      obtain ⟨hT, hN, hloss⟩ := hS T hTS
      let := hN
      let E := F.event T hT
      let D := V.event_loss T hT
      have hleft : 𝓝[<] T ≤ 𝓝[F.time_domain ∩ Iio T] T := by
        rw [← nhdsWithin_Ico_eq_nhdsLT E.tMinus_lt]
        exact nhdsWithin_mono _ (fun t ht =>
          ⟨C.nonempty_pre_interval T hT ht, ht.2⟩)
      exact ⟨D.left_limit_volume, D.left_limit_volume_tendsto.mono_left hleft,
        (add_le_add le_rfl hloss).trans
          (D.terminal_volume_drop.trans D.regular_limit_volume_le_left_limit)⟩)
  have hsum := (le_add_of_nonneg_left (bot_le : (0 : ℝ≥0∞) ≤
    ENNReal.ofReal (Real.exp (-(6 * b))) *
      calibratedMetricVolume (F.metric b) univ)).trans hbalance
  simpa only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using hsum

end PoincareMT.SurgeryFiniteness
