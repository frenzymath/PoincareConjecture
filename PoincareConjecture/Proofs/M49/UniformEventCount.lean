import PoincareConjecture.Proofs.M49.UniformCapCount
import PoincareConjecture.Proofs.M49.ComponentHistory










set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators

universe u

namespace PoincareConjecture.M49



theorem exists_uniform_event_prefix_bound
    (c d B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hV₀ : V₀ ≠ ⊤) (hhMin : 0 < hMin) :
    ∃ N : ℕ, ∀ (F : SurgeryFlowData.{u}) (b : ℝ),
      b ∈ F.time_domain → b ≤ B →
      (∀ t ∈ Icc 0 b, SurgeryPinchedAt (F.connection t) t) →
      (∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Icc 0 b →
        ∀ [Nonempty (F.slice T).carrier], (F.event T hT).cap_count = 0 →
          ∃ x : (F.slice (F.event T hT).tMinus).carrier,
            connectedComponent x ⊆ (F.event T hT).retained_preᶜ) →
      calibratedMetricVolume (F.metric 0) univ ≤ V₀ →
      (∀ T ∈ F.surgery_times ∩ Icc 0 b,
        F.parameters.delta T ≤ d ∧ hMin ≤ F.parameters.h T) →
      (∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Icc 0 b →
        ∀ [Nonempty (F.slice T).carrier],
          calibratedMetricVolume (F.metric T) univ +
              ((F.event T hT).cap_count : ℝ≥0∞) *
                ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) ≤
            calibratedMetricVolume (F.event T hT).limit_metric univ) →
      ∀ S : Finset ℝ, (S : Set ℝ) ⊆ F.surgery_times ∩ Icc 0 b → S.card ≤ N := by
  classical
  obtain ⟨Nc, hNc⟩ := exists_uniform_cap_count_bound c d B V₀ hMin hc hd hV₀ hhMin
  obtain ⟨N₀, hN₀⟩ := exists_uniform_initial_component_bound V₀ hV₀
  refine ⟨N₀ + 2 * Nc, ?_⟩
  intro F b hb hbB hpinched hdiscard hvol hscale hdrop S hS
  have hfinite : (F.surgery_times ∩ Ioc 0 b).Finite :=
    (surgeryTimes_inter_Icc_finite F F.zero_mem hb).subset
      (inter_subset_inter_right _ Ioc_subset_Icc_self)
  let A := hfinite.toFinset
  have hA : (A : Set ℝ) = F.surgery_times ∩ Ioc 0 b := hfinite.coe_toFinset
  have hAI : (A : Set ℝ) ⊆ F.surgery_times ∩ Icc 0 b := by
    rw [hA]
    exact inter_subset_inter_right _ Ioc_subset_Icc_self
  have hSA : S ⊆ A := by
    intro T hTS
    have hT := hS hTS
    change T ∈ (A : Set ℝ)
    rw [hA]
    exact ⟨hT.1, surgeryTime_pos F hT.1, hT.2.2⟩
  have hcap := hNc F b hb hbB hpinched hvol hscale hdrop A hAI
  have hcomponent := event_card_le_initial_add_twice_caps F hb hdiscard A hA
  have hinitial := hN₀ F hvol
  have hcard := Finset.card_le_card hSA
  omega

end PoincareConjecture.M49
