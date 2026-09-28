import PoincareConjecture.Proofs.M49.SlabVolume
import PoincareConjecture.Proofs.M49.Mathlib.FiniteJumps










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M49



theorem volume_growth_of_event_drops (H : GeneralizedParabolicRescalingTheory.{u} 3)
    (F : SurgeryFlowData.{u}) {a b : ℝ} (ha : a ∈ F.time_domain)
    (hb : b ∈ F.time_domain) (hab : a ≤ b)
    (hpinched : ∀ t ∈ Icc a b, SurgeryPinchedAt (F.connection t) t)
    (hdrop : ∀ T ∈ F.surgery_times ∩ Ioc a b, ∃ L : ℝ≥0∞,
      Tendsto (fun t => calibratedMetricVolume (F.metric t) univ)
        (𝓝[F.time_domain ∩ Iio T] T) (𝓝 L) ∧
      calibratedMetricVolume (F.metric T) univ ≤ L) :
    calibratedMetricVolume (F.metric b) univ ≤
      ENNReal.ofReal (Real.exp (6 * (b - a))) * calibratedMetricVolume (F.metric a) univ := by
  classical
  let V := fun t => calibratedMetricVolume (F.metric t) univ
  let w := fun t => ENNReal.ofReal (Real.exp (-(6 * t))) * V t
  have hfinite : (F.surgery_times ∩ Ioc a b).Finite :=
    (surgeryTimes_inter_Icc_finite F ha hb).subset
      (inter_subset_inter_right _ Ioc_subset_Icc_self)
  let S := hfinite.toFinset
  have hmem (t : ℝ) : t ∈ S ↔ t ∈ F.surgery_times ∩ Ioc a b := hfinite.mem_toFinset
  have hJ : Icc a b ⊆ F.time_domain := F.time_domain_interval.out ha hb
  have hw : w b ≤ w a := by
    apply le_of_finite_left_jumps S hab (fun t ht => ((hmem t).mp ht).2)
    · intro x hx y hy hxy hdisjoint
      have hno : Disjoint F.surgery_times (Ioc x y) := by
        apply disjoint_left.mpr
        intro z hz hzxy
        exact disjoint_left.mp hdisjoint
          ((hmem z).mpr ⟨hz, hx.1.trans_lt hzxy.1, hzxy.2.trans hy.2⟩) hzxy
      have hxyJ : Icc x y ⊆ Icc a b := fun r hr =>
        ⟨hx.1.trans hr.1, hr.2.trans hy.2⟩
      have hv := regular_volume_le_exp_mul H F hxy (hxyJ.trans hJ) hno
        (fun r hr => hpinched r (hxyJ hr))
      have hw' := mul_le_mul_right hv (ENNReal.ofReal (Real.exp (-(6 * y))))
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at hw'
      have he : -(6 * y) + 6 * (y - x) = -(6 * x) := by ring
      rw [he] at hw'
      exact hw'
    · intro T hTS
      have hT := (hmem T).mp hTS
      obtain ⟨L, hlim, hVT⟩ := hdrop T hT
      have hleft : 𝓝[<] T ≤ 𝓝[F.time_domain ∩ Iio T] T := by
        rw [← nhdsWithin_Ico_eq_nhdsLT hT.2.1]
        apply nhdsWithin_mono
        intro t ht
        exact ⟨hJ ⟨ht.1, ht.2.le.trans hT.2.2⟩, ht.2⟩
      have hweight : Continuous (fun t : ℝ => ENNReal.ofReal (Real.exp (-(6 * t)))) :=
        ENNReal.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
      refine ⟨ENNReal.ofReal (Real.exp (-(6 * T))) * L, ?_, mul_le_mul_right hVT _⟩
      exact ENNReal.Tendsto.mul
        ((hweight.tendsto T).mono_left nhdsWithin_le_nhds)
        (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))
        (hlim.mono_left hleft) (Or.inr ENNReal.ofReal_ne_top)
  calc
    V b = ENNReal.ofReal (Real.exp (6 * b)) * w b := by
      dsimp [w]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (6 * b)) * w a := mul_le_mul_right hw _
    _ = _ := by
      dsimp [w, V]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have he : 6 * b + -(6 * a) = 6 * (b - a) := by ring
      rw [he]



theorem volume_growth_of_event_losses (H : GeneralizedParabolicRescalingTheory.{u} 3)
    (F : SurgeryFlowData.{u})
    (E : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
      ∀ [Nonempty (F.slice T).carrier], RepairedSurgeryEventLossData F T hT)
    {a b : ℝ} (ha : a ∈ F.time_domain) (hb : b ∈ F.time_domain) (hab : a ≤ b)
    (hpinched : ∀ t ∈ Icc a b, SurgeryPinchedAt (F.connection t) t) :
    calibratedMetricVolume (F.metric b) univ ≤
      ENNReal.ofReal (Real.exp (6 * (b - a))) * calibratedMetricVolume (F.metric a) univ := by
  apply volume_growth_of_event_drops H F ha hb hab hpinched
  intro T hT
  rcases isEmpty_or_nonempty (F.slice T).carrier with hEmpty | hNonempty
  · let := hEmpty
    let D := F.vanishing_event T hT.1
    refine ⟨D.left_limit_volume,
      D.left_limit_volume_tendsto.mono_left (nhdsWithin_mono _ inter_subset_right), ?_⟩
    rw [univ_eq_empty_iff.mpr hEmpty, measure_empty]
    exact bot_le
  · let := hNonempty
    let D := E T hT.1
    refine ⟨D.left_limit_volume, D.left_limit_volume_tendsto, ?_⟩
    exact (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ D.loss from bot_le)).trans
      (D.terminal_volume_drop.trans D.regular_limit_volume_le_left_limit)

end PoincareConjecture.M49
