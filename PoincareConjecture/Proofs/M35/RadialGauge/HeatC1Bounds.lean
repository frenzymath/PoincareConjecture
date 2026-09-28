import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelLinearity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))


noncomputable def heatC1Gain (n : ℕ) (t : ℝ) : ℝ :=
  max (t * (1 + Real.sqrt (2 * t) * gaussianFirstMoment n))
    (2 * gaussianFirstMoment n * Real.sqrt t + gaussianSecondMoment n * t)

theorem heatC1Gain_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ heatC1Gain n t := by
  have hm : 0 ≤ gaussianFirstMoment n := gaussianFirstMoment_nonneg
  apply le_trans _ (le_max_left _ _)
  exact mul_nonneg ht (by positivity)

theorem heatC1Gain_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    heatC1Gain n s ≤ heatC1Gain n t := by
  have hm : 0 ≤ gaussianFirstMoment n := gaussianFirstMoment_nonneg
  apply max_le_max
  · apply mul_le_mul hst _ (by positivity) (hst.trans' hs)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hst (by norm_num))) gaussianFirstMoment_nonneg
  · exact add_le_add
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hst)
        (mul_nonneg (by norm_num) gaussianFirstMoment_nonneg))
      (mul_le_mul_of_nonneg_left hst gaussianSecondMoment_nonneg)


theorem exists_pos_heatC1Gain_lt {e : ℝ} (he : 0 < e) :
    ∃ t : ℝ, 0 < t ∧ heatC1Gain n t < e := by
  have hc : Continuous (heatC1Gain n) := by unfold heatC1Gain; fun_prop
  have hlim : Tendsto (heatC1Gain n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [heatC1Gain] using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsmall := (tendsto_order.mp hlim).2 e he
  have hp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hte⟩ := (hp.and hsmall).exists
  exact ⟨t, ht, hte⟩



theorem heatDuhamel_c1_bound {f : ℝ → V → F} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (f s))
    (hdf : ∀ s ∈ Ico 0 t, ∃ B : ℝ, ∀ x, ‖fderiv ℝ (f s) x‖ ≤ B)
    (hfb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    (1 + ‖x‖) * ‖heatDuhamel f t x‖ ≤ C * heatC1Gain (n + 1) t ∧
    (1 + ‖x‖) * ‖fderiv ℝ (heatDuhamel f t) x‖ ≤ C * heatC1Gain (n + 1) t := by
  constructor
  · apply (heatDuhamel_weighted_norm_le hC ht (fun s hs => (hf s hs).continuous) hfb x).trans
    calc
      _ = C * (t * (1 + Real.sqrt (2 * t) * gaussianFirstMoment (n + 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hC
  · rw [heatDuhamel_fderiv_eq hC ht hfm hf hdf hfb x]
    exact (heatDuhamelGradient_weighted_norm_le hC ht
      (fun s hs => (hf s hs).continuous) hfb x).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hC)



theorem heatDuhamel_c1_difference_bound {f g : ℝ → V → F} {C D H t : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hgm : StronglyMeasurable (Function.uncurry g))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (f s))
    (hg : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (g s))
    (hdf : ∀ s ∈ Ico 0 t, ∃ B : ℝ, ∀ x, ‖fderiv ℝ (f s) x‖ ≤ B)
    (hdg : ∀ s ∈ Ico 0 t, ∃ B : ℝ, ∀ x, ‖fderiv ℝ (g s) x‖ ≤ B)
    (hfb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C)
    (hgb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖g s x‖ ≤ D)
    (hfg : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x - g s x‖ ≤ H) (x : V) :
    (1 + ‖x‖) * ‖heatDuhamel f t x - heatDuhamel g t x‖ ≤ H * heatC1Gain (n + 1) t ∧
    (1 + ‖x‖) * ‖fderiv ℝ (heatDuhamel f t) x - fderiv ℝ (heatDuhamel g t) x‖ ≤
      H * heatC1Gain (n + 1) t := by
  have hfc s hs := (hf s hs).continuous
  have hgc s hs := (hg s hs).continuous
  constructor
  · rw [← heatDuhamel_sub ht hfm hgm hfc hgc hfb hgb x]
    have h := heatDuhamel_weighted_norm_le hH ht
      (fun s hs => (hfc s hs).sub (hgc s hs)) hfg x
    apply h.trans
    calc
      _ = H * (t * (1 + Real.sqrt (2 * t) * gaussianFirstMoment (n + 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hH
  · rw [heatDuhamel_fderiv_eq hC ht hfm hf hdf hfb x,
      heatDuhamel_fderiv_eq hD ht hgm hg hdg hgb x,
      ← heatDuhamelGradient_sub hC hD ht hfm hgm hfc hgc hfb hgb x]
    exact (heatDuhamelGradient_weighted_norm_le hH ht
      (fun s hs => (hfc s hs).sub (hgc s hs)) hfg x).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hH)

end PoincareConjecture.M35.RadialGauge
