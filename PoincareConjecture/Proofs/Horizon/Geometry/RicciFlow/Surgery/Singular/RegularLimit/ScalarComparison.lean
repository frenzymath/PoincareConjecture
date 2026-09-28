import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set

namespace PoincareConjecture.SingularRegularLimit

private theorem exists_first_level {f : ℝ → ℝ} {a b H : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < H) (hb : H ≤ f b) :
    ∃ c ∈ Ioc a b, f c = H ∧ ∀ t ∈ Ico a c, f t < H := by
  let S := Icc a b ∩ f ⁻¹' {H}
  have hS : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
  obtain ⟨c, hc, hmin⟩ := hS.exists_isMinOn ⟨x, hx, hfx⟩ continuousOn_id
  have hcH : f c = H := hc.2
  have hac : a < c := lt_of_le_of_ne hc.1.1 (by
    intro h
    subst c
    exact ha.ne hcH)
  refine ⟨c, ⟨hac, hc.1.2⟩, hcH, ?_⟩
  intro t ht
  by_contra h
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc ht.1
    (hf.mono (Icc_subset_Icc le_rfl (ht.2.le.trans hc.1.2)))
    ⟨ha.le, le_of_not_gt h⟩
  have hcu : c ≤ u := hmin ⟨⟨hu.1, hu.2.trans (ht.2.le.trans hc.1.2)⟩, hfu⟩
  exact (not_lt_of_ge (hcu.trans hu.2)) ht.2

private theorem exists_last_level_below {f : ℝ → ℝ} {a b H : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : H ≤ f a) (hb : f b < H) :
    ∃ c ∈ Ico a b, f c = H ∧ ∀ t ∈ Ioc c b, f t < H := by
  let S := Icc a b ∩ f ⁻¹' {H}
  have hS : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hf ⟨hb.le, ha⟩
  obtain ⟨c, hc, hmax⟩ := hS.exists_isMaxOn ⟨x, hx, hfx⟩ continuousOn_id
  have hcH : f c = H := hc.2
  have hcb : c < b := lt_of_le_of_ne hc.1.2 (by
    intro h
    subst c
    exact hb.ne hcH)
  refine ⟨c, ⟨hc.1.1, hcb⟩, hcH, ?_⟩
  intro t ht
  by_contra h
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' ht.2
    (hf.mono (Icc_subset_Icc (hc.1.1.trans ht.1.le) le_rfl))
    ⟨hb.le, le_of_not_gt h⟩
  have huc : u ≤ c := hmax ⟨⟨(hc.1.1.trans ht.1.le).trans hu.1, hu.2⟩, hfu⟩
  exact (not_lt_of_ge (hu.1.trans huc)) ht.1

private theorem exists_last_level_above {f : ℝ → ℝ} {a b H : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ H) (hb : H < f b) :
    ∃ c ∈ Ico a b, f c = H ∧ ∀ t ∈ Ioc c b, H < f t := by
  obtain ⟨c, hc, he, hafter⟩ := exists_last_level_below hab hf.neg
    (neg_le_neg ha) (neg_lt_neg hb)
  exact ⟨c, hc, neg_injective he, fun t ht => neg_lt_neg_iff.mp (hafter t ht)⟩

theorem scalar_lt_two_mul_of_short_interval {f : ℝ → ℝ} {s T C rho K : ℝ}
    (hC : 0 ≤ C) (hrho : 0 < rho) (hrhoK : rho ≤ K)
    (hf : ContinuousOn f (Icc s T)) (hs : f s < K)
    (hd : ∀ t ∈ Ioo s T, rho ≤ f t →
      ∃ d, HasDerivAt f d t ∧ |d| ≤ C * f t ^ 2)
    (hshort : T - s < 1 / (4 * (C + 1) * K)) :
    ∀ t ∈ Icc s T, f t < 2 * K := by
  have hK : 0 < K := hrho.trans_le hrhoK
  intro t ht
  by_contra hbad
  have hst : ContinuousOn f (Icc s t) := hf.mono (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨v, hv, hfv, hbefore⟩ := exists_first_level ht.1 hst
    (by linarith : f s < 2 * K) (le_of_not_gt hbad)
  have hsv : ContinuousOn f (Icc s v) := hst.mono (Icc_subset_Icc le_rfl hv.2)
  obtain ⟨u, hu, hfu, hafter⟩ := exists_last_level_above hv.1.le hsv
    hs.le (by rw [hfv]; linarith)
  have huv : ContinuousOn f (Icc u v) := hsv.mono (Icc_subset_Icc hu.1 le_rfl)
  have hder : ∀ z ∈ Ioo u v, ∃ d, HasDerivAt f d z ∧ |d| ≤ 4 * C * K ^ 2 := by
    intro z hz
    have hlo := hafter z ⟨hz.1, hz.2.le⟩
    have hhi := hbefore z ⟨hu.1.trans hz.1.le, hz.2⟩
    obtain ⟨d, hdz, hbound⟩ := hd z
      ⟨hu.1.trans_lt hz.1, hz.2.trans_le (hv.2.trans ht.2)⟩
      (hrhoK.trans hlo.le)
    refine ⟨d, hdz, hbound.trans ?_⟩
    have hsq : f z ^ 2 ≤ 4 * K ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  have hdiff : DifferentiableOn ℝ f (Ioo u v) := by
    intro z hz
    obtain ⟨d, hdz, _⟩ := hder z hz
    exact hdz.differentiableAt.differentiableWithinAt
  obtain ⟨z, hz, he⟩ := exists_deriv_eq_slope f hu.2 huv hdiff
  obtain ⟨d, hdz, hbound⟩ := hder z hz
  rw [hdz.deriv, hfv, hfu] at he
  have hslope : K ≤ (4 * C * K ^ 2) * (v - u) := by
    have hb : (2 * K - K) / (v - u) ≤ 4 * C * K ^ 2 :=
      he ▸ (le_abs_self d).trans hbound
    have := (div_le_iff₀ (sub_pos.mpr hu.2)).mp hb
    linarith
  have htime : (v - u) * (4 * (C + 1) * K) < 1 := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * (C + 1) * K)).mp
    exact lt_of_le_of_lt (sub_le_sub (hv.2.trans ht.2) hu.1) hshort
  have hmul := mul_lt_mul_of_pos_right htime hK
  have hnonneg : 0 ≤ K ^ 2 * (v - u) :=
    mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hu.2.le)
  nlinarith

theorem scalar_lt_two_mul_of_short_tail {f : ℝ → ℝ} {s T C rho K : ℝ}
    (hC : 0 ≤ C) (hrho : 0 < rho) (hrhoK : rho ≤ K)
    (hf : ContinuousOn f (Ico s T)) (hs : f s < K)
    (hd : ∀ t ∈ Ioo s T, rho ≤ f t →
      ∃ d, HasDerivAt f d t ∧ |d| ≤ C * f t ^ 2)
    (hshort : T - s < 1 / (4 * (C + 1) * K)) :
    ∀ t ∈ Ico s T, f t < 2 * K := by
  intro t ht
  exact scalar_lt_two_mul_of_short_interval hC hrho hrhoK
    (hf.mono (fun z hz => ⟨hz.1, hz.2.trans_lt ht.2⟩)) hs
    (fun z hz => hd z ⟨hz.1, hz.2.trans ht.2⟩)
    ((sub_le_sub_right ht.2.le s).trans_lt hshort) t ⟨ht.1, le_rfl⟩

theorem scalar_lt_two_mul_of_short_interval_backward {f : ℝ → ℝ} {s T C rho K : ℝ}
    (hC : 0 ≤ C) (hrho : 0 < rho) (hrhoK : rho ≤ K)
    (hf : ContinuousOn f (Icc s T)) (hT : f T < K)
    (hd : ∀ t ∈ Ioo s T, rho ≤ f t →
      ∃ d, HasDerivAt f d t ∧ |d| ≤ C * f t ^ 2)
    (hshort : T - s < 1 / (4 * (C + 1) * K)) :
    ∀ t ∈ Icc s T, f t < 2 * K := by
  have hc : ContinuousOn (fun t => f (-t)) (Icc (-T) (-s)) :=
    hf.comp continuous_neg.continuousOn (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hd' : ∀ t ∈ Ioo (-T) (-s), rho ≤ f (-t) →
      ∃ d, HasDerivAt (fun z => f (-z)) d t ∧ |d| ≤ C * f (-t) ^ 2 := by
    intro t ht hR
    obtain ⟨d, hdf, hbound⟩ := hd (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ hR
    refine ⟨-d, ?_, by simpa only [abs_neg] using hbound⟩
    simpa only [Function.comp_def, neg_mul, mul_one, mul_neg, id_eq] using
      hdf.comp t (hasDerivAt_id t).neg
  intro t ht
  have h := scalar_lt_two_mul_of_short_interval hC hrho hrhoK hc
    (by simpa only [neg_neg] using hT) hd' (by linarith) (-t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [neg_neg] using h

end PoincareConjecture.SingularRegularLimit
