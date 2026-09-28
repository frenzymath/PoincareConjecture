import PoincareConjecture.Proofs.M49.DirectLeftLimitVolume
import PoincareConjecture.Proofs.M49.Mathlib.ExponentialJumpBalance










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M49



theorem weighted_event_losses_le_initial
    (F : SurgeryFlowData.{u}) {b : ℝ} (hb : b ∈ F.time_domain)
    (hpinched : ∀ t ∈ Icc 0 b, SurgeryPinchedAt (F.connection t) t)
    (loss : ℝ → ℝ≥0∞)
    (hvanish : ∀ T ∈ F.surgery_times ∩ Icc 0 b,
      IsEmpty (F.slice T).carrier → loss T = 0)
    (hdrop : ∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Icc 0 b →
      ∀ [Nonempty (F.slice T).carrier],
        calibratedMetricVolume (F.metric T) univ + loss T ≤
          calibratedMetricVolume (F.event T hT).limit_metric univ)
    (S : Finset ℝ) (hS : (S : Set ℝ) ⊆ F.surgery_times ∩ Icc 0 b) :
    ∑ T ∈ S, ENNReal.ofReal (Real.exp (-(6 * T))) * loss T ≤
      calibratedMetricVolume (F.metric 0) univ := by
  classical
  have hb0 : 0 ≤ b := F.time_domain_nonnegative hb
  have hJ : Icc 0 b ⊆ F.time_domain := initialInterval_subset F hb
  have hfinite : (F.surgery_times ∩ Ioc 0 b).Finite :=
    (surgeryTimes_inter_Icc_finite F F.zero_mem hb).subset
      (inter_subset_inter_right _ Ioc_subset_Icc_self)
  let A := hfinite.toFinset
  have hmem (t : ℝ) : t ∈ A ↔ t ∈ F.surgery_times ∩ Ioc 0 b := hfinite.mem_toFinset
  have hbalance := ENNReal.expWeighted_add_sum_le_of_finite_left_jumps 6
    (V := fun t => calibratedMetricVolume (F.metric t) univ) (loss := loss)
    A hb0 (fun t ht => ((hmem t).mp ht).2) (by
      intro x hx y hy hxy hdis
      have hno : Disjoint F.surgery_times (Ioc x y) := by
        apply disjoint_left.mpr
        intro z hz hxy'
        exact disjoint_left.mp hdis
          ((hmem z).mpr ⟨hz, hx.1.trans_lt hxy'.1, hxy'.2.trans hy.2⟩) hxy'
      have hsub : Icc x y ⊆ Icc 0 b := fun t ht =>
        ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
      exact regular_volume_le_exp_mul_direct F hxy (hsub.trans hJ) hno
        (fun t ht => hpinched t (hsub ht))) (by
      intro T hTA
      have hT := (hmem T).mp hTA
      have hTI : T ∈ Icc 0 b := Ioc_subset_Icc_self hT.2
      rcases isEmpty_or_nonempty (F.slice T).carrier with hEmpty | hNonempty
      · let := hEmpty
        let E := F.vanishing_event T hT.1
        refine ⟨E.left_limit_volume, E.left_limit_volume_tendsto, ?_⟩
        rw [univ_eq_empty_iff.mpr hEmpty, measure_empty,
          hvanish T ⟨hT.1, hTI⟩ hEmpty, zero_add]
        exact bot_le
      · let := hNonempty
        let E := F.event T hT.1
        obtain ⟨L, _hL, hlim⟩ := preEvent_exists_finite_left_limit_direct F T hT.1
          (fun t ht => hpinched t ⟨E.tMinus_nonnegative.trans ht.1,
            ht.2.le.trans hTI.2⟩)
        have hleft : 𝓝[<] T ≤ 𝓝[F.time_domain ∩ Iio T] T := by
          rw [← nhdsWithin_Ico_eq_nhdsLT E.tMinus_lt]
          exact nhdsWithin_mono _ (fun t ht =>
            ⟨nonemptyEventPreInterval F T hT.1 ht, ht.2⟩)
        exact ⟨L, hlim.mono_left hleft,
          (hdrop T hT.1 hTI).trans
            (event_regular_limit_volume_le_left_limit_direct F T hT.1 hlim)⟩)
  have hA : ∑ T ∈ A, ENNReal.ofReal (Real.exp (-(6 * T))) * loss T ≤
      calibratedMetricVolume (F.metric 0) univ := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (le_add_of_nonneg_left (bot_le : (0 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (-(6 * b))) *
          calibratedMetricVolume (F.metric b) univ)).trans hbalance
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; exact bot_le)) hA
  intro T hTS
  have hT := hS hTS
  exact (hmem T).mpr ⟨hT.1, surgeryTime_pos F hT.1, hT.2.2⟩

end PoincareConjecture.M49
