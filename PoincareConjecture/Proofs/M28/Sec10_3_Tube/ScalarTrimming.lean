import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CounterexamplePath

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28

private theorem exists_first_scalar_level {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a < c) (hb : c ≤ f b) :
    ∃ s ∈ Icc a b, f s = c ∧ ∀ t ∈ Ico a s, f t < c := by
  let K : Set ℝ := Icc a b ∩ f ⁻¹' {c}
  have hclosed : IsClosed K :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨s₀, hs₀, heq₀⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
  have hnonempty : K.Nonempty := ⟨s₀, hs₀, heq₀⟩
  obtain ⟨s, hs, hleast⟩ := hcompact.exists_isLeast hnonempty
  refine ⟨s, hs.1, hs.2, ?_⟩
  intro t ht
  by_contra h
  have hft : c ≤ f t := le_of_not_gt h
  have hsubset : Icc a t ⊆ Icc a b :=
    Icc_subset_Icc le_rfl (ht.2.le.trans hs.1.2)
  obtain ⟨v, hv, heq⟩ := intermediate_value_Icc ht.1 (hf.mono hsubset) ⟨ha.le, hft⟩
  have hsv : s ≤ v := hleast ⟨hsubset hv, heq⟩
  exact (not_lt_of_ge hsv) (hv.2.trans_lt ht.2)

theorem exists_scalar_band_subinterval {f : ℝ → ℝ} {a b low high : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a < low) (hlevels : low < high) (hb : high < f b) :
    ∃ s t : ℝ, a < s ∧ s < t ∧ t < b ∧ f s = low ∧ f t = high ∧
      ∀ v ∈ Icc s t, f v ∈ Icc low high := by
  obtain ⟨t, ht, htval, hbefore⟩ :=
    exists_first_scalar_level hab hf (ha.trans hlevels) hb.le
  have hsubset : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  obtain ⟨s, hs, hsval, hafter⟩ :=
    exists_last_eq_of_continuousOn ht.1 (hf.mono hsubset) ha.le
      (by simpa only [htval] using hlevels)
  have has : a < s := by
    by_contra h
    have hsa : s = a := le_antisymm (le_of_not_gt h) hs.1
    rw [hsa] at hsval
    exact (ne_of_lt ha) hsval
  have hst : s < t := by
    by_contra h
    have hst' : s = t := le_antisymm hs.2 (le_of_not_gt h)
    rw [hst', htval] at hsval
    exact (ne_of_lt hlevels) hsval.symm
  have htb : t < b := by
    by_contra h
    have htb' : t = b := le_antisymm ht.2 (le_of_not_gt h)
    rw [htb'] at htval
    exact (ne_of_lt hb) htval.symm
  refine ⟨s, t, has, hst, htb, hsval, htval, ?_⟩
  intro v hv
  constructor
  · rcases eq_or_lt_of_le hv.1 with hvs | hvs
    · simpa only [← hvs] using hsval.ge
    · exact (hafter v ⟨hvs, hv.2⟩).le
  · rcases eq_or_lt_of_le hv.2 with hvt | hvt
    · simpa only [hvt] using htval.le
    · exact (hbefore v ⟨hs.1.trans hv.1, hvt⟩).le

theorem exists_claim10_4_scalar_band {f : ℝ → ℝ} {a b B Q : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hB : 2 ≤ B) (hQ : 0 < Q) (ha : f a ≤ 8 * Q)
    (hb : 32 * B ^ 2 * Q < f b) :
    ∃ s t : ℝ, a < s ∧ s < t ∧ t < b ∧
      f s = 16 * B * Q ∧ f t = f b / (2 * B) ∧
      ∀ v ∈ Icc s t, f v ∈ Icc (16 * B * Q) (f b / (2 * B)) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hden : 0 < 2 * B := mul_pos (by norm_num) hBpos
  have hstart : f a < 16 * B * Q :=
    ha.trans_lt (mul_lt_mul_of_pos_right (by linarith only [hB]) hQ)
  have hlevels : 16 * B * Q < f b / (2 * B) := by
    apply (lt_div_iff₀ hden).mpr
    calc
      16 * B * Q * (2 * B) = 32 * B ^ 2 * Q := by ring
      _ < f b := hb
  have hfb : 0 < f b := lt_trans (by positivity) hb
  have hend : f b / (2 * B) < f b :=
    div_lt_self hfb (by linarith only [hB])
  exact exists_scalar_band_subinterval hab hf hstart hlevels hend

theorem CounterexamplePathSegment.exists_trimmed_scalar_band
    (P : RicciFlowCurvatureTheory.{u}) {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    (S : CounterexamplePathSegment E) (hD₀ : 0 < D₀)
    (hD : 32 * (max C 2) ^ 2 ≤ D) :
    let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
    let R := fun v : ℝ => E.flow.scalar ⟨E.time, S.path v⟩
    let B := max C 2
    ∃ s t : ℝ, S.level_parameter < s ∧ s < t ∧ t < 1 ∧
      R s = 16 * B * Q ∧ R t = R 1 / (2 * B) ∧
      (∀ v ∈ Icc s t, R v ∈ Icc (16 * B * Q) (R 1 / (2 * B))) ∧
      (E.flow.metric E.time).pathELength S.path s t <
        ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) ∧
      ∀ v ∈ Icc s t,
        Nonempty (GeneralizedCanonicalControl (F := E.flow) E.time (S.path v) epsilon C) := by
  dsimp only
  let Q := E.flow.scalar ⟨E.time, E.basepoint⟩
  let R := fun v : ℝ => E.flow.scalar ⟨E.time, S.path v⟩
  let B := max C 2
  have hQ : 0 < Q := lt_of_lt_of_le hD₀ E.base_lower
  have hR : ContinuousOn R (Icc S.level_parameter 1) :=
    (E.flow.continuous_scalar_slice P E.time).comp_continuousOn
      S.path_smooth.continuous.continuousOn
  have hstart : R S.level_parameter ≤ 8 * Q := by
    change E.flow.scalar ⟨E.time, S.path S.level_parameter⟩ ≤ 8 * Q
    rw [S.level_eq]
    change 4 * Q ≤ 8 * Q
    nlinarith only [hQ]
  have hend : 32 * B ^ 2 * Q < R 1 := by
    have hproduct : 32 * B ^ 2 * Q ≤ D * Q :=
      mul_le_mul_of_nonneg_right hD hQ.le
    exact hproduct.trans_lt (by simpa only [R, Q, S.path_one] using E.scalar_large)
  obtain ⟨s, t, has, hst, htb, hsval, htval, hband⟩ :=
    exists_claim10_4_scalar_band S.level_mem.2 hR (le_max_right C 2) hQ hstart hend
  refine ⟨s, t, has, hst, htb, hsval, htval, hband, ?_, ?_⟩
  · let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (E.flow.slice E.time).carrier → Type _) :=
      ⟨(E.flow.metric E.time).toRiemannianMetric⟩
    exact (Manifold.pathELength_mono has.le htb.le).trans_lt S.suffix_length
  · intro v hv
    exact S.canonical_after v ⟨has.le.trans hv.1, hv.2.trans htb.le⟩

end PoincareConjecture.M28
