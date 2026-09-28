import PoincareConjecture.Definitions.M49VolumeLoss
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {F : SurgeryFlowData.{u}} {C : RepairedVolumeLossControls F}

theorem m52VolumeBoundOnCompacts (V : RepairedVolumeLossData F C)
    (Kset : Set ℝ) (hK : IsCompact Kset) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ t ∈ F.time_domain ∩ Kset,
      calibratedMetricVolume (F.metric t) Set.univ ≤ B := by
  obtain ⟨H, hH⟩ := hK.bddAbove
  refine ⟨ENNReal.ofReal (Real.exp (6 * H)) *
    calibratedMetricVolume (F.metric 0) Set.univ,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top V.initial_volume_ne_top, ?_⟩
  intro t ht
  have hgrowth := V.volume_growth 0 t F.zero_mem ht.1
    (F.time_domain_nonnegative ht.1)
  simp only [sub_zero] at hgrowth
  refine hgrowth.trans (mul_le_mul_left ?_ _)
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hH ht.2) (by norm_num)))

theorem m52VolumeLossOnCompacts (V : RepairedVolumeLossData F C)
    (Kset : Set ℝ) (hK : IsCompact Kset) :
    ∃ loss : ∀ (T : ℝ) (_hT : T ∈ F.surgery_times)
        [Nonempty (F.slice T).carrier], ℝ≥0∞,
      ∃ sigma : ℝ, 0 < sigma ∧
        ∀ T hT [Nonempty (F.slice T).carrier], T ∈ Kset →
          (calibratedMetricVolume (F.metric T) Set.univ + loss T hT ≤
              calibratedMetricVolume (F.event T hT).limit_metric Set.univ ∧
           ((loss T hT ≠ 0 ∧
            loss T hT ≤ calibratedMetricVolume (F.event T hT).limit_metric Set.univ) ∨
           (loss T hT = 0 ∧ (F.event T hT).cap_count = 0)) ∧
           (0 < (F.event T hT).cap_count → ENNReal.ofReal sigma ≤ loss T hT)) := by
  obtain ⟨H, hH⟩ := hK.bddAbove
  obtain ⟨sigma, hpos, hbound⟩ := V.horn_loss_lower_bound (max 0 H) (le_max_left _ _)
  refine ⟨fun T hT => (V.event_loss T hT).loss, sigma, hpos, ?_⟩
  intro T hT hN hTK
  let W := V.event_loss T hT
  refine ⟨W.terminal_volume_drop, ?_, ?_⟩
  · rcases W.event_case with ⟨i, hpositive, _⟩ | ⟨hcap, hzero, _⟩
    · exact Or.inl ⟨ne_of_gt hpositive,
        (le_add_left (le_refl W.loss)).trans W.terminal_volume_drop⟩
    · exact Or.inr ⟨hzero, hcap⟩
  · intro hcap
    exact (hbound T hT
      ⟨F.time_domain_nonnegative (F.surgery_times_subset hT),
        (hH hTK).trans (le_max_right _ _)⟩ hcap).1

theorem m52ComponentEventCountOnCompacts (V : RepairedVolumeLossData F C)
    (Kset : Set ℝ) (hK : IsCompact Kset) :
    ∃ n : ℕ, ∀ S : Finset ℝ,
      (↑S : Set ℝ) ⊆ {T ∈ F.surgery_times ∩ Kset |
        ∀ (hT : T ∈ F.surgery_times) (hN : Nonempty (F.slice T).carrier),
          letI := hN
          (F.event T hT).cap_count = 0} → S.card ≤ n := by
  classical
  obtain ⟨H, hH⟩ := hK.bddAbove
  obtain ⟨n, hcount⟩ := V.component_event_count_bound (max 0 H) (le_max_left _ _)
  refine ⟨n, ?_⟩
  intro S hS
  apply hcount S
  intro T hT
  obtain ⟨⟨hevent, hTK⟩, hcap⟩ := hS hT
  refine ⟨⟨hevent, F.time_domain_nonnegative (F.surgery_times_subset hevent),
    (hH hTK).trans (le_max_right _ _)⟩, hevent, ?_⟩
  by_cases hN : Nonempty (F.slice T).carrier
  · exact Or.inr ⟨hN, hcap hevent hN⟩
  · exact Or.inl (not_nonempty_iff.mp hN)

theorem m52VolumeGrowthOnCompacts (V : RepairedVolumeLossData F C)
    (Kset : Set ℝ) (_hK : IsCompact Kset) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℝ,
      a ∈ F.time_domain ∩ Kset → b ∈ F.time_domain ∩ Kset → a ≤ b →
      calibratedMetricVolume (F.metric b) Set.univ ≤
        ENNReal.ofReal (Real.exp (B * (b - a))) *
          calibratedMetricVolume (F.metric a) Set.univ := by
  exact ⟨6, by norm_num, fun a b ha hb hab => V.volume_growth a b ha.1 hb.1 hab⟩

end PoincareConjecture
