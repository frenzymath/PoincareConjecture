import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ExtendedExcursion
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.GeneralPosition.ConvexSegmentNeighborhood
import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcNesting

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_flattened_excursion_in_convex_tube_unordered
    {r q : ℝ → V} (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hq : FinitePiecewiseAffineOn q (Icc 0 1)) (hi : InjOn q (Icc 0 1))
    {u v δ : ℝ} (huv : u < v) (hδ : 0 < δ)
    (hpositive : ∀ x ∈ Ioo u v, 0 < (r x).2)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - v))
    (hfixed : ∀ x ∈ Icc (0 : ℝ) 1 \ Ioo u v, q x = r x)
    (hflat : q '' Icc u v = segment ℝ (r u) (r v))
    {U : Set V} (hU : IsOpen U) (hbaseU : segment ℝ (r u) (r v) ⊆ U) :
    ∃ (ε l t : ℝ) (C : Set V), 0 < ε ∧ ε < δ ∧
      0 < l ∧ l < u ∧ v < t ∧ t < 1 ∧ IsOpen C ∧ Convex ℝ C ∧ C ⊆ U ∧
      IsFinitePLBallPair ℝ (q '' Icc l t) {q l, q t} ∧ q '' Icc l t ⊆ C ∧
      q l ≠ q t ∧ ((r u).1 < (r v).1 → (q l).1 < (q t).1) ∧
      (q l).2 = -ε ∧ (q t).2 = -ε ∧
      (q '' Icc l t) ∩ {x | x.2 = -ε} = {q l, q t} ∧
      (∀ x ∈ Ioo l t, -ε < (q x).2) ∧
      (∀ x ∈ Icc l t, (q x).2 ≤ 0) ∧
      (q '' Icc l t) ∩ {x | x.2 = 0} = segment ℝ (r u) (r v) ∧
      u - l < δ ∧ t - v < δ := by
  obtain ⟨a₀, b₀, m₀, ha₀, hau, hub, hb₀, hm₀, hf₀⟩ := hleft
  obtain ⟨a₁, b₁, m₁, ha₁, hav, hvb, hb₁, hm₁, hf₁⟩ := hright
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨ha₀.trans hau.le, hub.le.trans hb₀⟩
  have hv : v ∈ Icc (0 : ℝ) 1 := ⟨ha₁.trans hav.le, hvb.le.trans hb₁⟩
  have hru : (r u).2 = 0 := by simpa using hf₀ u ⟨hau.le, hub.le⟩
  have hrv : (r v).2 = 0 := by simpa using hf₁ v ⟨hav.le, hvb.le⟩
  obtain ⟨ρ, hC, hρ, hCopen, hCconvex, hbaseC, hCU, hballL, hballR⟩ :=
    exists_convex_segment_neighborhood hU hbaseU
  have hqu : q u = r u := hfixed u ⟨hu, by simp⟩
  have hqv : q v = r v := hfixed v ⟨hv, by simp⟩
  have hne : (r v).1 - (r u).1 ≠ 0 := by
    intro he
    have hp : r u = r v := Prod.ext (by linarith) (hru.trans hrv.symm)
    exact huv.ne (hi hu hv (hqu.trans (hp.trans hqv.symm)))
  let η := min ρ (|(r v).1 - (r u).1| / 3)
  have hη : 0 < η := lt_min hρ (div_pos (abs_pos.mpr hne) (by norm_num))
  obtain ⟨δL, hδL, hcloseL⟩ := Metric.continuousWithinAt_iff.mp (hr.continuousOn u hu) η hη
  obtain ⟨δR, hδR, hcloseR⟩ := Metric.continuousWithinAt_iff.mp (hr.continuousOn v hv) η hη
  let δ' := min δ (min δL δR)
  have hδ' : 0 < δ' := lt_min hδ (lt_min hδL hδR)
  obtain ⟨ε, l, t, hε, hεδ', hl, hlu, hvt, ht, hrl, hrt, hpos, hnegL, hnegR, hlclose, htclose⟩ :=
    exists_lower_level_extension_of_transverse_excursion huv hδ' hpositive
      ⟨a₀, b₀, m₀, ha₀, hau, hub, hb₀, hm₀, by simpa using hf₀⟩
      ⟨a₁, b₁, m₁, ha₁, hav, hvb, hb₁, hm₁, by simpa using hf₁⟩
  have hlt : l < t := hlu.trans (huv.trans hvt)
  have hsub : Icc l t ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨hl.le.trans hx.1, hx.2.trans ht.le⟩
  have hleftclose (x : ℝ) (hx : x ∈ Icc l u) : dist (r x) (r u) < η := by
    apply hcloseL ⟨hl.le.trans hx.1, hx.2.trans hu.2⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    have hh : δ' ≤ δL := (min_le_right _ _).trans (min_le_left _ _)
    linarith [hx.1]
  have hrightclose (x : ℝ) (hx : x ∈ Icc v t) : dist (r x) (r v) < η := by
    apply hcloseR ⟨hv.1.trans hx.1, hx.2.trans ht.le⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    have hh : δ' ≤ δR := (min_le_right _ _).trans (min_le_right _ _)
    linarith [hx.2]
  have hqleft (x : ℝ) (hx : x ∈ Icc l u) : q x = r x :=
    hfixed x ⟨⟨hl.le.trans hx.1, hx.2.trans hu.2⟩, fun h => (not_lt_of_ge hx.2) h.1⟩
  have hqright (x : ℝ) (hx : x ∈ Icc v t) : q x = r x :=
    hfixed x ⟨⟨hv.1.trans hx.1, hx.2.trans ht.le⟩, fun h => (not_lt_of_ge hx.1) h.2⟩
  have hqmiddle (x : ℝ) (hx : x ∈ Icc u v) : q x ∈ segment ℝ (r u) (r v) :=
    hflat.subset (mem_image_of_mem q hx)
  have hbasezero (x : V) (hx : x ∈ segment ℝ (r u) (r v)) : x.2 = 0 :=
    Polygon.segment_subset_returning_axis hru hrv hx
  have hball : IsFinitePLBallPair ℝ (q '' Icc l t) {q l, q t} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc hlt).image_of_subset hq hsub hi
  have hqC : q '' Icc l t ⊆ hC := by
    rintro x ⟨s, hs, rfl⟩
    by_cases hsu : s ≤ u
    · rw [hqleft s ⟨hs.1, hsu⟩]
      exact hballL ((hleftclose s ⟨hs.1, hsu⟩).trans_le (min_le_left _ _))
    · by_cases hvs : v ≤ s
      · rw [hqright s ⟨hvs, hs.2⟩]
        exact hballR ((hrightclose s ⟨hvs, hs.2⟩).trans_le (min_le_left _ _))
      · exact hbaseC (hqmiddle s ⟨(lt_of_not_ge hsu).le, (lt_of_not_ge hvs).le⟩)
  have hql : q l = r l := hqleft l ⟨le_rfl, hlu.le⟩
  have hqt : q t = r t := hqright t ⟨hvt.le, le_rfl⟩
  have hqlphase : (q l).2 = -ε := by simpa [hql] using hrl
  have hqtphase : (q t).2 = -ε := by simpa [hqt] using hrt
  have hnewpos (x : ℝ) (hx : x ∈ Ioo l t) : -ε < (q x).2 := by
    by_cases hsu : x ≤ u
    · rw [hqleft x ⟨hx.1.le, hsu⟩]
      simpa using hpos x hx
    · by_cases hvs : v ≤ x
      · rw [hqright x ⟨hvs, hx.2.le⟩]
        simpa using hpos x hx
      · rw [hbasezero _ (hqmiddle x ⟨(lt_of_not_ge hsu).le, (lt_of_not_ge hvs).le⟩)]
        linarith
  have hnewneg (x : ℝ) (hx : x ∈ Icc l t) : (q x).2 ≤ 0 := by
    by_cases hsu : x < u
    · rw [hqleft x ⟨hx.1, hsu.le⟩]
      exact (hnegL x ⟨hx.1, hsu⟩).le
    · by_cases hvs : v < x
      · rw [hqright x ⟨hvs.le, hx.2⟩]
        exact (hnegR x ⟨hvs, hx.2⟩).le
      · exact (hbasezero _ (hqmiddle x ⟨le_of_not_gt hsu, le_of_not_gt hvs⟩)).le
  refine ⟨ε, l, t, hC, hε, hεδ'.trans_le (min_le_left _ _), hl, hlu, hvt, ht,
    hCopen, hCconvex, hCU, hball, hqC, ?_, ?_, hqlphase, hqtphase, ?_, hnewpos, hnewneg,
    ?_, hlclose.trans_le (min_le_left _ _), htclose.trans_le (min_le_left _ _)⟩
  · exact fun he => hlt.ne (hi (hsub ⟨le_rfl, hlt.le⟩) (hsub ⟨hlt.le, le_rfl⟩) he)
  · intro horder
    rw [hql, hqt]
    have hlbound := (max_lt_iff.mp (show max (dist (r l).1 (r u).1)
      (dist (r l).2 (r u).2) < η from hleftclose l ⟨le_rfl, hlu.le⟩)).1
    have htbound := (max_lt_iff.mp (show max (dist (r t).1 (r v).1)
      (dist (r t).2 (r v).2) < η from hrightclose t ⟨hvt.le, le_rfl⟩)).1
    rw [Real.dist_eq] at hlbound htbound
    have hηsmall : η ≤ ((r v).1 - (r u).1) / 3 := by
      simpa only [η, abs_of_pos (sub_pos.mpr horder)] using (min_le_right ρ (|(r v).1 - (r u).1| / 3))
    linarith [(abs_lt.mp hlbound).2, (abs_lt.mp htbound).1]
  · apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hsc⟩
      by_cases hsl : s = l
      · simp [hsl]
      by_cases hst : s = t
      · simp [hst]
      have hh := hnewpos s ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hst⟩
      exact (not_lt_of_ge (le_of_eq hsc) hh).elim
    · rintro x (rfl | rfl)
      · exact ⟨mem_image_of_mem q ⟨le_rfl, hlt.le⟩, hqlphase⟩
      · exact ⟨mem_image_of_mem q ⟨hlt.le, le_rfl⟩, hqtphase⟩
  · apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hs0⟩
      by_cases hsu : s < u
      · rw [hqleft s ⟨hs.1, hsu.le⟩] at hs0
        exact ((ne_of_lt (hnegL s ⟨hs.1, hsu⟩)) hs0).elim
      by_cases hvs : v < s
      · rw [hqright s ⟨hvs.le, hs.2⟩] at hs0
        exact ((ne_of_lt (hnegR s ⟨hvs, hs.2⟩)) hs0).elim
      exact hqmiddle s ⟨le_of_not_gt hsu, le_of_not_gt hvs⟩
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := hflat.symm.subset hx
      exact ⟨mem_image_of_mem q ⟨hlu.le.trans hs.1, hs.2.trans hvt.le⟩,
        hbasezero _ (hqmiddle s hs)⟩

theorem exists_flattened_excursion_in_convex_tube
    {r q : ℝ → V} (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hq : FinitePiecewiseAffineOn q (Icc 0 1)) (hi : InjOn q (Icc 0 1))
    {u v δ : ℝ} (huv : u < v) (hδ : 0 < δ)
    (horder : (r u).1 < (r v).1)
    (hpositive : ∀ x ∈ Ioo u v, 0 < (r x).2)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - v))
    (hfixed : ∀ x ∈ Icc (0 : ℝ) 1 \ Ioo u v, q x = r x)
    (hflat : q '' Icc u v = segment ℝ (r u) (r v))
    {U : Set V} (hU : IsOpen U) (hbaseU : segment ℝ (r u) (r v) ⊆ U) :
    ∃ (ε l t : ℝ) (C : Set V), 0 < ε ∧ ε < δ ∧
      0 < l ∧ l < u ∧ v < t ∧ t < 1 ∧ IsOpen C ∧ Convex ℝ C ∧ C ⊆ U ∧
      IsFinitePLBallPair ℝ (q '' Icc l t) {q l, q t} ∧ q '' Icc l t ⊆ C ∧
      (q l).1 < (q t).1 ∧ (q l).2 = -ε ∧ (q t).2 = -ε ∧
      (q '' Icc l t) ∩ {x | x.2 = -ε} = {q l, q t} ∧
      (∀ x ∈ Ioo l t, -ε < (q x).2) ∧
      (∀ x ∈ Icc l t, (q x).2 ≤ 0) ∧
      (q '' Icc l t) ∩ {x | x.2 = 0} = segment ℝ (r u) (r v) := by
  obtain ⟨ε, l, t, C, hε, hεδ, hl, hlu, hvt, ht, ho, hc, hCU, hball, hinto,
    _, horder', hfl, hft, haxis, hpos, hneg, hzero, _, _⟩ :=
    exists_flattened_excursion_in_convex_tube_unordered hr hq hi huv hδ
      hpositive hleft hright hfixed hflat hU hbaseU
  exact ⟨ε, l, t, C, hε, hεδ, hl, hlu, hvt, ht, ho, hc, hCU, hball, hinto,
    horder' horder, hfl, hft, haxis, hpos, hneg, hzero⟩

end PoincareConjecture.M76.Dehn
