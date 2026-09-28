import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open scoped Topology

namespace Poincare

theorem nonneg_of_deriv_pos_on_neg
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : 0 ≤ f a)
    (hd : ∀ t ∈ Ioo a b, f t < 0 → ∃ d, HasDerivAt f d t ∧ 0 < d) :
    ∀ t ∈ Icc a b, 0 ≤ f t := by
  have hhalf : ∀ t ∈ Ico a b, 0 ≤ f t := by
    intro t ht
    by_contra hneg
    have hft : f t < 0 := lt_of_not_ge hneg
    obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr ht.1) (hf.mono (Icc_subset_Icc le_rfl ht.2.le))
    have hcneg : f c < 0 := (hmin ⟨ht.1, le_rfl⟩).trans_lt hft
    have hac : a < c := lt_of_le_of_ne hc.1 (by
      intro heq
      subst c
      exact (not_lt_of_ge ha) hcneg)
    obtain ⟨d, hcd, hdpos⟩ := hd c ⟨hac, hc.2.trans_lt ht.2⟩ hcneg
    have hslope : ∀ᶠ y in 𝓝[<] c, 0 < slope f c y :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp hcd).1 (Ioi_mem_nhds hdpos)
    obtain ⟨y, hypos, hy⟩ := (hslope.and (Ioo_mem_nhdsLT hac)).exists
    have hmy : f c ≤ f y := hmin ⟨hy.1.le, hy.2.le.trans hc.2⟩
    have hslopenonpos : slope f c y ≤ 0 := by
      rw [slope_def_field]
      exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmy)
        (sub_nonpos.mpr hy.2.le)
    exact (not_lt_of_ge hslopenonpos) hypos
  rcases hab.lt_or_eq with hab | rfl
  · intro t ht
    exact ContinuousWithinAt.closure_le
      (by simpa [closure_Ico hab.ne] using ht)
      continuousWithinAt_const ((hf t ht).mono Ico_subset_Icc_self) hhalf
  · simpa only [Icc_self, mem_singleton_iff, forall_eq] using ha

end Poincare
