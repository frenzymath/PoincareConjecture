import PoincareConjecture.Proofs.M49.WeightedEventVolume
import PoincareConjecture.Proofs.M49.FlowEventCounts










set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators

universe u

namespace PoincareConjecture.M49



theorem exists_uniform_cap_count_bound
    (c d B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hV₀ : V₀ ≠ ⊤) (hhMin : 0 < hMin) :
    ∃ N : ℕ, ∀ (F : SurgeryFlowData.{u}) (b : ℝ),
      b ∈ F.time_domain → b ≤ B →
      (∀ t ∈ Icc 0 b, SurgeryPinchedAt (F.connection t) t) →
      calibratedMetricVolume (F.metric 0) univ ≤ V₀ →
      (∀ T ∈ F.surgery_times ∩ Icc 0 b,
        F.parameters.delta T ≤ d ∧ hMin ≤ F.parameters.h T) →
      (∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Icc 0 b →
        ∀ [Nonempty (F.slice T).carrier],
          calibratedMetricVolume (F.metric T) univ +
              ((F.event T hT).cap_count : ℝ≥0∞) *
                ENNReal.ofReal (c * (F.parameters.h T ^ 3 / F.parameters.delta T)) ≤
            calibratedMetricVolume (F.event T hT).limit_metric univ) →
      ∀ S : Finset ℝ, (S : Set ℝ) ⊆ F.surgery_times ∩ Icc 0 b →
        ∑ T ∈ S, eventCapCount F T ≤ N := by
  let sigma := c * (hMin ^ 3 / d)
  have hsigma : 0 < sigma := mul_pos hc (div_pos (pow_pos hhMin 3) hd)
  let w := Real.exp (-(6 * B)) * sigma
  have hw : 0 < w := mul_pos (Real.exp_pos _) hsigma
  obtain ⟨N, hN⟩ := exists_nat_ge (V₀.toReal / w)
  refine ⟨N, ?_⟩
  intro F b hb hbB hpinched hvol hscale hdrop S hS
  have hlower (T : ℝ) (hT : T ∈ F.surgery_times ∩ Icc 0 b) :
      sigma ≤ c * (F.parameters.h T ^ 3 / F.parameters.delta T) := by
    have hdelta := F.parameters.delta_pos T hT.2.1
    have hh := (hscale T hT).2
    have hp : hMin ^ 3 ≤ F.parameters.h T ^ 3 := pow_le_pow_left₀ hhMin.le hh 3
    apply mul_le_mul_of_nonneg_left _ hc.le
    exact div_le_div₀ (pow_nonneg (hhMin.le.trans hh) 3) hp hdelta (hscale T hT).1
  let loss := fun T => (eventCapCount F T : ℝ≥0∞) * ENNReal.ofReal sigma
  have hsum := weighted_event_losses_le_initial F hb hpinched loss (by
    intro T _hT hEmpty
    let := hEmpty
    simp only [loss, eventCapCount_eq_zero_of_isEmpty, Nat.cast_zero, zero_mul]) (by
    intro T hT hTI hNonempty
    let := hNonempty
    dsimp [loss]
    rw [eventCapCount_eq F T hT]
    exact (add_le_add le_rfl
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hlower T ⟨hT, hTI⟩)))).trans
        (hdrop T hT hTI)) S hS
  have hbound : ((∑ T ∈ S, eventCapCount F T : ℕ) : ℝ≥0∞) * ENNReal.ofReal w ≤ V₀ := by
    calc
      _ = ∑ T ∈ S, (eventCapCount F T : ℝ≥0∞) * ENNReal.ofReal w := by
        rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ ∑ T ∈ S, ENNReal.ofReal (Real.exp (-(6 * T))) * loss T := by
        apply Finset.sum_le_sum
        intro T hTS
        have hTB := (hS hTS).2.2.trans hbB
        have hexp : Real.exp (-(6 * B)) ≤ Real.exp (-(6 * T)) :=
          Real.exp_le_exp.mpr (by linarith)
        calc
          _ = ENNReal.ofReal (Real.exp (-(6 * B))) * loss T := by
            rw [show w = Real.exp (-(6 * B)) * sigma from rfl,
              ENNReal.ofReal_mul (Real.exp_pos _).le]
            dsimp [loss]
            ac_rfl
          _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl
      _ ≤ V₀ := hsum.trans hvol
  have hreal := ENNReal.toReal_mono hV₀ hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hw.le] at hreal
  exact_mod_cast (((le_div_iff₀ hw).mpr hreal).trans hN)

end PoincareConjecture.M49
