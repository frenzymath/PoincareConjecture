import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.TimeSegments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

theorem ae_graph_joinTime {E F : Type*} (I : E → F)
    {v₁ v₂ : ℝ → E} {U₁ U₂ : ℝ → F} {S T : ℝ}
    (h₁ : ∀ᵐ t ∂timeMeasure S, I (v₁ t) = U₁ t)
    (h₂ : ∀ᵐ t ∂timeMeasure T, I (v₂ t) = U₂ t) :
    ∀ᵐ t ∂timeMeasure (S + T), I (joinTime v₁ v₂ S t) = joinTime U₁ U₂ S t := by
  have hg : ∀ᵐ t ∂volume.restrict (Ioc S (S + T)), I (v₂ (t - S)) = U₂ (t - S) :=
    (measurePreserving_sub_time S T).quasiMeasurePreserving.ae h₂
  have hl := (ae_restrict_iff' measurableSet_Ioc).mp h₁
  have hr := (ae_restrict_iff' measurableSet_Ioc).mp hg
  filter_upwards [ae_restrict_of_ae hl, ae_restrict_of_ae hr,
    ae_restrict_mem measurableSet_Ioc] with t hleft hright ht
  by_cases hts : t ≤ S
  · simp only [joinTime, if_pos hts]
    exact hleft ⟨ht.1, hts⟩
  · simp only [joinTime, if_neg hts]
    exact hright ⟨lt_of_not_ge hts, ht.2⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_joinTime_left (f g : ℝ → E) {S t : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) :
    ∫ s in (0 : ℝ)..t, joinTime f g S s = ∫ s in (0 : ℝ)..t, f s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact if_pos (hs.2.trans htS)

theorem integral_joinTime_right (f g : ℝ → E) {S t : ℝ} (hS : 0 ≤ S) (hSt : S ≤ t)
    (hf : IntervalIntegrable f volume 0 S) (hg : IntervalIntegrable g volume 0 (t - S)) :
    ∫ s in (0 : ℝ)..t, joinTime f g S s =
      (∫ s in (0 : ℝ)..S, f s) + ∫ s in (0 : ℝ)..(t - S), g s := by
  have hl : EqOn f (joinTime f g S) (uIoc 0 S) := by
    rw [uIoc_of_le hS]
    intro s hs
    exact (if_pos hs.2).symm
  have hr : EqOn (fun s => g (s - S)) (joinTime f g S) (uIoc S t) := by
    rw [uIoc_of_le hSt]
    intro s hs
    exact (if_neg (not_le.mpr hs.1)).symm
  have hgs : IntervalIntegrable (fun s => g (s - S)) volume S t := by
    simpa only [zero_add, sub_add_cancel] using hg.comp_sub_right S
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.congr hl) (hgs.congr hr),
    integral_joinTime_left f g hS le_rfl]
  congr 1
  calc
    (∫ s in S..t, joinTime f g S s) = ∫ s in S..t, g (s - S) := by
      apply intervalIntegral.integral_congr_ae_restrict
      exact (ae_restrict_mem measurableSet_uIoc).mono (fun s hs => (hr hs).symm)
    _ = _ := by rw [intervalIntegral.integral_comp_sub_right, sub_self]

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
