import PoincareConjecture.Proofs.M50.Lemma17_12_Telescoping
import PoincareConjecture.Proofs.M50.Mathlib.FiniteCardBound











set_option autoImplicit false

open Set
open scoped ENNReal BigOperators

universe u

namespace PoincareConjecture.M50



theorem cap_event_count_bound
    (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F)
    (V : RepairedVolumeLossData F C) (H : ℝ) (hH : 0 ≤ H) :
    ∃ n : ℕ, ∀ S : Finset ℝ,
      (↑S : Set ℝ) ⊆ {T ∈ F.surgery_times ∩ Icc 0 H |
        ∃ hT : T ∈ F.surgery_times,
          ∃ hN : Nonempty (F.slice T).carrier,
            letI := hN
            0 < (F.event T hT).cap_count} →
      S.card ≤ n := by
  obtain ⟨sigma, hsigma, hlower⟩ := V.horn_loss_lower_bound H hH
  let w := Real.exp (-(6 * H)) * sigma
  have hw : 0 < w := mul_pos (Real.exp_pos _) hsigma
  obtain ⟨n, hn⟩ := exists_nat_ge
    ((calibratedMetricVolume (F.metric 0) univ).toReal / w)
  refine ⟨n, ?_⟩
  intro S hS
  have hsum := weighted_constant_losses_le_initial F C V sigma S (by
    intro T hTS
    obtain ⟨hTI, hT, hN, hcap⟩ := hS hTS
    let := hN
    exact ⟨hT, hN, (hlower T hT hTI.2 hcap).1⟩)
  have hbound : (S.card : ℝ≥0∞) * ENNReal.ofReal w ≤
      calibratedMetricVolume (F.metric 0) univ := by
    calc
      _ = ∑ _T ∈ S, ENNReal.ofReal w := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ S, ENNReal.ofReal (Real.exp (-(6 * T))) *
          ENNReal.ofReal sigma := by
        apply Finset.sum_le_sum
        intro T hTS
        have hTH := (hS hTS).1.2.2
        have hexp : Real.exp (-(6 * H)) ≤ Real.exp (-(6 * T)) :=
          Real.exp_le_exp.mpr (by linarith)
        rw [show w = Real.exp (-(6 * H)) * sigma from rfl,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl
      _ ≤ _ := hsum
  have hreal := ENNReal.toReal_mono V.initial_volume_ne_top hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hw.le] at hreal
  exact_mod_cast (((le_div_iff₀ hw).mpr hreal).trans hn)



theorem surgery_times_inter_Icc_finite
    (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F)
    (V : RepairedVolumeLossData F C) (H : ℝ) (hH : 0 ≤ H) :
    (F.surgery_times ∩ Icc 0 H).Finite := by
  obtain ⟨ncap, hcap⟩ := cap_event_count_bound F C V H hH
  obtain ⟨ncomp, hcomp⟩ := V.component_event_count_bound H hH
  have hcapfinite := Set.finite_of_forall_finset_card_le _ ncap hcap
  have hcompfinite := Set.finite_of_forall_finset_card_le _ ncomp hcomp
  apply (hcapfinite.union hcompfinite).subset
  intro T hTI
  rcases isEmpty_or_nonempty (F.slice T).carrier with hEmpty | hNonempty
  · exact Or.inr ⟨hTI, hTI.1, Or.inl hEmpty⟩
  · let := hNonempty
    by_cases hzero : (F.event T hTI.1).cap_count = 0
    · exact Or.inr ⟨hTI, hTI.1, Or.inr ⟨hNonempty, hzero⟩⟩
    · exact Or.inl ⟨hTI, hTI.1, hNonempty, Nat.pos_of_ne_zero hzero⟩

end PoincareConjecture.M50
