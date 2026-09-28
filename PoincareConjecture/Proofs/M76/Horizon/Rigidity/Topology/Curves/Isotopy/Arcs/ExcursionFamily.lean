import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.GenericAxis
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Excursion



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_positive_excursion_of_endpoint_lt {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c x : ℝ}
    (h0 : f 0 < c) (h1 : f 1 < c) (hx : x ∈ Icc (0 : ℝ) 1) (hfx : c < f x) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧
      f a = c ∧ f b = c ∧ ∀ y ∈ Ioo a b, c < f y := by
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hx.1
    (hf.continuousOn.mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)) ⟨h0.le, hfx.le⟩
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hx.2
    (hf.continuousOn.mono (fun y hy => ⟨hx.1.trans hy.1, hy.2⟩)) ⟨h1.le, hfx.le⟩
  have hux : u < x := lt_of_le_of_ne hu.2 (by intro h; rw [h] at hfu; linarith)
  have hxv : x < v := lt_of_le_of_ne hv.1 (by intro h; rw [← h] at hfv; linarith)
  obtain ⟨a, b, hua, hax, hxb, hbv, hfa, hfb, hpos⟩ :=
    exists_positive_finitePL_excursion hf hu.1 hux hxv hv.2 hfu hfv hfx
  exact ⟨a, b, hu.1.trans hua, hax, hxb, hbv.trans hv.2, hfa, hfb, hpos⟩

theorem no_positive_regular_local_minimum {f : ℝ → ℝ} {c x a b : ℝ}
    (hax : a < x) (hxb : x < b)
    (hleft : ∀ y ∈ Ioo a x, c < f y) (hright : ∀ y ∈ Ioo x b, c < f y)
    (hreg : ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
      ∀ y ∈ Icc u v, f y - c = m * (y - x)) : False := by
  obtain ⟨u, v, m, hux, hxv, hm, hformula⟩ := hreg
  obtain ⟨l, hl0, hl1⟩ := exists_between (max_lt hax hux)
  obtain ⟨r, hr0, hr1⟩ := exists_between (lt_min hxb hxv)
  have hlpos := hleft l ⟨(le_max_left a u).trans_lt hl0, hl1⟩
  have hrpos := hright r ⟨hr0, hr1.trans_le (min_le_left b v)⟩
  have hfl := hformula l ⟨((le_max_right a u).trans_lt hl0).le, hl1.le.trans hxv.le⟩
  have hfr := hformula r ⟨hux.le.trans hr0.le, (hr1.trans_le (min_le_right b v)).le⟩
  rcases lt_or_gt_of_ne hm with hm | hm
  · have := mul_neg_of_neg_of_pos hm (sub_pos.mpr hr0)
    linarith
  · have := mul_neg_of_pos_of_neg hm (sub_neg.mpr hl1)
    linarith

theorem positive_excursion_intervals_disjoint {f : ℝ → ℝ} {c : ℝ}
    (hreg : ∀ x ∈ Icc (0 : ℝ) 1, f x = c →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, f y - c = m * (y - x))
    {a b d e : ℝ} (hab : a < b) (hde : d < e)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hd0 : 0 ≤ d) (he1 : e ≤ 1)
    (hfa : f a = c) (hfb : f b = c) (hfd : f d = c) (hfe : f e = c)
    (hpos : ∀ y ∈ Ioo a b, c < f y) (hpos' : ∀ y ∈ Ioo d e, c < f y)
    (hne : (a, b) ≠ (d, e)) : Disjoint (Icc a b) (Icc d e) := by
  have hordered {a b d e : ℝ} (hab : a < b) (hde : d < e)
      (hb : b ∈ Icc (0 : ℝ) 1) (hfb : f b = c) (hfd : f d = c)
      (hpos : ∀ y ∈ Ioo a b, c < f y) (hpos' : ∀ y ∈ Ioo d e, c < f y)
      (had : a < d) : b < d := by
    by_contra h
    have hdb : d ≤ b := le_of_not_gt h
    rcases hdb.eq_or_lt with hdb | hdb
    · subst d
      exact no_positive_regular_local_minimum hab hde hpos hpos' (hreg b hb hfb)
    · have := hpos d ⟨had, hdb⟩
      linarith
  rcases lt_trichotomy a d with had | had | hda
  · exact disjoint_left.mpr (fun x hx hy =>
      (not_le_of_gt (hordered hab hde ⟨ha0.trans hab.le, hb1⟩ hfb hfd hpos hpos' had))
        (hy.1.trans hx.2))
  · subst d
    have hbe : b = e := by
      rcases lt_trichotomy b e with hbe | hbe | heb
      · have := hpos' b ⟨hab, hbe⟩
        linarith
      · exact hbe
      · have := hpos e ⟨hde, heb⟩
        linarith
    exact (hne (Prod.ext rfl hbe)).elim
  · exact disjoint_left.mpr (fun x hx hy =>
      (not_le_of_gt (hordered hde hab ⟨hd0.trans hde.le, he1⟩ hfe hfa hpos' hpos hda))
        (hx.1.trans hy.2))

private theorem exists_excursion_containing_regular_contact {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c x : ℝ}
    (h0 : f 0 < c) (h1 : f 1 < c) (hx : x ∈ Icc (0 : ℝ) 1) (hfx : f x = c)
    (hreg : ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
      ∀ y ∈ Icc u v, f y - c = m * (y - x)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ f a = c ∧ f b = c ∧
      (∀ y ∈ Ioo a b, c < f y) ∧ x ∈ Icc a b := by
  have hx0 : 0 < x := lt_of_le_of_ne hx.1 (by intro h; rw [← h] at hfx; linarith)
  have hx1 : x < 1 := lt_of_le_of_ne hx.2 (by intro h; rw [h] at hfx; linarith)
  obtain ⟨u, v, m, hux, hxv, hm, hformula⟩ := hreg
  rcases lt_or_gt_of_ne hm with hm | hm
  · obtain ⟨z, hz0, hzx⟩ := exists_between (max_lt hux hx0)
    have hzu : u < z := (le_max_left u 0).trans_lt hz0
    have hzI : z ∈ Icc (0 : ℝ) 1 :=
      ⟨((le_max_right u 0).trans_lt hz0).le, hzx.le.trans hx.2⟩
    have hfz := hformula z ⟨hzu.le, hzx.le.trans hxv.le⟩
    have hpz : c < f z := by
      have := mul_pos_of_neg_of_neg hm (sub_neg.mpr hzx)
      linarith
    obtain ⟨a, b, ha0, haz, hzb, hb1, hfa, hfb, hpos⟩ :=
      exists_positive_excursion_of_endpoint_lt hf h0 h1 hzI hpz
    refine ⟨a, b, ha0, haz.trans hzb, hb1, hfa, hfb, hpos,
      (haz.trans hzx).le, ?_⟩
    by_contra h
    have hbx : b < x := lt_of_not_ge h
    have hformulaB := hformula b ⟨(hzu.trans hzb).le, (hbx.trans hxv).le⟩
    have := mul_pos_of_neg_of_neg hm (sub_neg.mpr hbx)
    rw [hfb] at hformulaB
    linarith
  · obtain ⟨z, hxz, hz1⟩ := exists_between (lt_min hxv hx1)
    have hzv : z < v := hz1.trans_le (min_le_left v 1)
    have hzI : z ∈ Icc (0 : ℝ) 1 :=
      ⟨hx.1.trans hxz.le, (hz1.trans_le (min_le_right v 1)).le⟩
    have hfz := hformula z ⟨hux.le.trans hxz.le, hzv.le⟩
    have hpz : c < f z := by
      have := mul_pos hm (sub_pos.mpr hxz)
      linarith
    obtain ⟨a, b, ha0, haz, hzb, hb1, hfa, hfb, hpos⟩ :=
      exists_positive_excursion_of_endpoint_lt hf h0 h1 hzI hpz
    refine ⟨a, b, ha0, haz.trans hzb, hb1, hfa, hfb, hpos,
      ?_, (hxz.trans hzb).le⟩
    by_contra h
    have hxa : x < a := lt_of_not_ge h
    have hformulaA := hformula a ⟨(hux.trans hxa).le, (haz.trans hzv).le⟩
    have := mul_pos hm (sub_pos.mpr hxa)
    rw [hfa] at hformulaA
    linarith

theorem exists_finite_positive_excursion_family {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c : ℝ}
    (h0 : f 0 < c) (h1 : f 1 < c)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | f x = c}.Finite)
    (hreg : ∀ x ∈ Icc (0 : ℝ) 1, f x = c →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, f y - c = m * (y - x)) :
    ∃ J : Finset (ℝ × ℝ),
      (∀ p ∈ J, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧ f p.1 = c ∧ f p.2 = c ∧
        ∀ y ∈ Ioo p.1 p.2, c < f y) ∧
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (Icc p.1 p.2) (Icc q.1 q.2)) ∧
      {x ∈ Icc (0 : ℝ) 1 | c ≤ f x} = ⋃ p ∈ J, Icc p.1 p.2 := by
  classical
  let P : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
    f p.1 = c ∧ f p.2 = c ∧ ∀ y ∈ Ioo p.1 p.2, c < f y}
  have hP : P.Finite := (hfinite.prod hfinite).subset (by
    rintro p ⟨ha, hab, hb, hfa, hfb, _⟩
    exact ⟨⟨⟨ha, hab.le.trans hb⟩, hfa⟩, ⟨⟨ha.trans hab.le, hb⟩, hfb⟩⟩)
  refine ⟨hP.toFinset, ?_, ?_, ?_⟩
  · intro p hp
    exact hP.mem_toFinset.mp hp
  · intro p hp q hq hne
    obtain ⟨ha, hab, hb, hfa, hfb, hpos⟩ := hP.mem_toFinset.mp hp
    obtain ⟨hd, hde, he, hfd, hfe, hpos'⟩ := hP.mem_toFinset.mp hq
    exact positive_excursion_intervals_disjoint hreg hab hde ha hb hd he
      hfa hfb hfd hfe hpos hpos' (by simpa only [Prod.mk.eta] using hne)
  · apply Subset.antisymm
    · rintro x ⟨hx, hfx⟩
      rcases hfx.eq_or_lt with hfx | hfx
      · obtain ⟨a, b, ha, hab, hb, hfa, hfb, hpos, hxab⟩ :=
          exists_excursion_containing_regular_contact hf h0 h1 hx hfx.symm
            (hreg x hx hfx.symm)
        exact mem_iUnion₂.mpr ⟨(a, b), hP.mem_toFinset.mpr
          ⟨ha, hab, hb, hfa, hfb, hpos⟩, hxab⟩
      · obtain ⟨a, b, ha, hax, hxb, hb, hfa, hfb, hpos⟩ :=
          exists_positive_excursion_of_endpoint_lt hf h0 h1 hx hfx
        exact mem_iUnion₂.mpr ⟨(a, b), hP.mem_toFinset.mpr
          ⟨ha, hax.trans hxb, hb, hfa, hfb, hpos⟩, hax.le, hxb.le⟩
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
      obtain ⟨ha, hab, hb, hfa, hfb, hpos⟩ := hP.mem_toFinset.mp hp
      refine ⟨⟨ha.trans hxp.1, hxp.2.trans hb⟩, ?_⟩
      rcases hxp.1.eq_or_lt with h | h
      · rw [← h, hfa]
      · rcases hxp.2.eq_or_lt with h' | h'
        · rw [h', hfb]
        · exact (hpos x ⟨h, h'⟩).le

end PoincareConjecture.M76.Dehn
