import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Excursion



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_lower_level_extension_of_transverse_excursion
    {f : ℝ → ℝ} {u v c δ : ℝ} (huv : u < v) (hδ : 0 < δ)
    (hpositive : ∀ x ∈ Ioo u v, c < f x)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, f x - c = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, f x - c = m * (x - v)) :
    ∃ ε l r : ℝ, 0 < ε ∧ ε < δ ∧ 0 < l ∧ l < u ∧ v < r ∧ r < 1 ∧
      f l = c - ε ∧ f r = c - ε ∧
      (∀ x ∈ Ioo l r, c - ε < f x) ∧
      (∀ x ∈ Ico l u, f x < c) ∧ (∀ x ∈ Ioc v r, f x < c) ∧
      u - l < δ ∧ r - v < δ := by
  obtain ⟨a₀, b₀, m₀, ha₀, hau, hub, hb₀, hm₀, hf₀⟩ := hleft
  obtain ⟨a₁, b₁, m₁, ha₁, hav, hvb, hb₁, hm₁, hf₁⟩ := hright
  have hm₀pos : 0 < m₀ := by
    obtain ⟨x, hux, hx⟩ := exists_between (lt_min hub huv)
    have hp := hpositive x ⟨hux, (lt_min_iff.mp hx).2⟩
    have he := hf₀ x ⟨hau.le.trans hux.le, (lt_min_iff.mp hx).1.le⟩
    nlinarith
  have hm₁neg : m₁ < 0 := by
    obtain ⟨x, hx, hxv⟩ := exists_between (max_lt hav huv)
    have hp := hpositive x ⟨(max_lt_iff.mp hx).2, hxv⟩
    have he := hf₁ x ⟨(max_lt_iff.mp hx).1.le, hxv.le.trans hvb.le⟩
    nlinarith
  have heps : 0 < min δ (min (m₀ * min (u - a₀) δ) ((-m₁) * min (b₁ - v) δ)) :=
    lt_min hδ (lt_min (mul_pos hm₀pos (lt_min (sub_pos.mpr hau) hδ))
      (mul_pos (neg_pos.mpr hm₁neg) (lt_min (sub_pos.mpr hvb) hδ)))
  obtain ⟨ε, hε, hεsmall⟩ := exists_between heps
  have hεδ : ε < δ := (lt_min_iff.mp hεsmall).1
  have hεLmin := (lt_min_iff.mp (lt_min_iff.mp hεsmall).2).1
  have hεRmin := (lt_min_iff.mp (lt_min_iff.mp hεsmall).2).2
  have hεL : ε < m₀ * (u - a₀) := hεLmin.trans_le
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hm₀pos.le)
  have hεR : ε < (-m₁) * (b₁ - v) := hεRmin.trans_le
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (neg_pos.mpr hm₁neg).le)
  have hεLδ : ε < m₀ * δ := hεLmin.trans_le
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hm₀pos.le)
  have hεRδ : ε < (-m₁) * δ := hεRmin.trans_le
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (neg_pos.mpr hm₁neg).le)
  let l := u - ε / m₀
  let r := v + ε / (-m₁)
  have hlnear : a₀ < l := by
    have hh : ε / m₀ < u - a₀ := (div_lt_iff₀ hm₀pos).mpr (by nlinarith)
    dsimp [l]
    linarith
  have hlu : l < u := by dsimp [l]; exact sub_lt_self _ (div_pos hε hm₀pos)
  have hvr : v < r := by dsimp [r]; exact lt_add_of_pos_right _ (div_pos hε (by linarith))
  have hrnear : r < b₁ := by
    have hh : ε / (-m₁) < b₁ - v := (div_lt_iff₀ (by linarith)).mpr (by nlinarith)
    dsimp [r]
    linarith
  have hlval : m₀ * (l - u) = -ε := by dsimp [l]; field_simp; ring
  have hrval : m₁ * (r - v) = -ε := by dsimp [r]; field_simp; ring
  have hfl : f l = c - ε := by
    have hh := hf₀ l ⟨hlnear.le, hlu.le.trans hub.le⟩
    rw [hlval] at hh
    linarith
  have hfr : f r = c - ε := by
    have hh := hf₁ r ⟨hav.le.trans hvr.le, hrnear.le⟩
    rw [hrval] at hh
    linarith
  refine ⟨ε, l, r, hε, hεδ, ha₀.trans_lt hlnear, hlu, hvr,
    hrnear.trans_le hb₁, hfl, hfr, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxu : x ≤ u
    · have he := hf₀ x ⟨hlnear.le.trans hx.1.le, hxu.trans hub.le⟩
      nlinarith [hx.1]
    · by_cases hvx : v ≤ x
      · have he := hf₁ x ⟨hav.le.trans hvx, hx.2.le.trans hrnear.le⟩
        nlinarith [hx.2]
      · exact (sub_lt_self c hε).trans (hpositive x ⟨lt_of_not_ge hxu, lt_of_not_ge hvx⟩)
  · intro x hx
    have he := hf₀ x ⟨hlnear.le.trans hx.1, hx.2.le.trans hub.le⟩
    nlinarith [hx.2]
  · intro x hx
    have he := hf₁ x ⟨hav.le.trans hx.1.le, hx.2.trans hrnear.le⟩
    nlinarith [hx.1]
  · have hh := (div_lt_iff₀ hm₀pos).mpr (by nlinarith : ε < δ * m₀)
    dsimp [l]
    linarith
  · have hh := (div_lt_iff₀ (neg_pos.mpr hm₁neg)).mpr
      (by nlinarith : ε < δ * (-m₁))
    dsimp [r]
    linarith

theorem exists_extended_finitePL_returning_arc
    {r : ℝ → ℝ × ℝ} (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hinj : InjOn r (Icc 0 1)) {u v c δ : ℝ} (huv : u < v) (hδ : 0 < δ)
    (hpositive : ∀ x ∈ Ioo u v, c < (r x).2)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 - c = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 - c = m * (x - v)) :
    ∃ ε l t : ℝ, 0 < ε ∧ ε < δ ∧ 0 < l ∧ l < u ∧ v < t ∧ t < 1 ∧
      (r l).2 = c - ε ∧ (r t).2 = c - ε ∧
      IsFinitePLBallPair ℝ (r '' Icc l t) {r l, r t} ∧
      (r '' Icc l t) ∩ {x | x.2 = c - ε} = {r l, r t} ∧
      (∀ x ∈ Ioo l t, c - ε < (r x).2) ∧
      (∀ x ∈ Ico l u, (r x).2 < c) ∧ (∀ x ∈ Ioc v t, (r x).2 < c) ∧
      u - l < δ ∧ t - v < δ := by
  obtain ⟨ε, l, t, hε, hεδ, hl, hlu, hvt, ht, hfl, hft, hpos, hnegL, hnegR, hcloseL, hcloseR⟩ :=
    exists_lower_level_extension_of_transverse_excursion huv hδ hpositive hleft hright
  have hlt : l < t := hlu.trans (huv.trans hvt)
  have hsub : Icc l t ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨hl.le.trans hx.1, hx.2.trans ht.le⟩
  have hball : IsFinitePLBallPair ℝ (r '' Icc l t) {r l, r t} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc hlt).image_of_subset hr hsub hinj
  refine ⟨ε, l, t, hε, hεδ, hl, hlu, hvt, ht, hfl, hft, hball, ?_, hpos, hnegL, hnegR,
    hcloseL, hcloseR⟩
  apply Subset.antisymm
  · rintro x ⟨⟨s, hs, rfl⟩, hsc⟩
    by_cases hsl : s = l
    · simp [hsl]
    by_cases hst : s = t
    · simp [hst]
    have hh := hpos s ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hst⟩
    exact (not_lt_of_ge (le_of_eq hsc) hh).elim
  · rintro x (rfl | rfl)
    · exact ⟨mem_image_of_mem r ⟨le_rfl, hlt.le⟩, hfl⟩
    · exact ⟨mem_image_of_mem r ⟨hlt.le, le_rfl⟩, hft⟩

end PoincareConjecture.M76.Dehn
