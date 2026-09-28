import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.ExcursionFamily

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_maximal_positive_interval {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c x : ℝ}
    (hfinite : {y ∈ Icc (0 : ℝ) 1 | f y = c}.Finite)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hfx : c < f x) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧
      (a = 0 ∨ f a = c) ∧ (b = 1 ∨ f b = c) ∧
      c ≤ f a ∧ c ≤ f b ∧ ∀ y ∈ Ioo a b, c < f y := by
  let Z : Set ℝ := {0, 1} ∪ {y ∈ Icc (0 : ℝ) 1 | f y = c}
  have hZ : Z.Finite := (show ({0, 1} : Set ℝ).Finite by simp).union hfinite
  obtain ⟨a, ha, hamax⟩ := (hZ.isCompact.inter_right isClosed_Icc).exists_isGreatest
    (show (Z ∩ Icc 0 x).Nonempty from ⟨0, Or.inl (by simp), le_rfl, hx.1.le⟩)
  obtain ⟨b, hb, hbmin⟩ := (hZ.isCompact.inter_right isClosed_Icc).exists_isLeast
    (show (Z ∩ Icc x 1).Nonempty from ⟨1, Or.inl (by simp), hx.2.le, le_rfl⟩)
  have hxZ : x ∉ Z := by
    rintro (h | h)
    · rcases h with h | h
      · have : x = 0 := h
        linarith [hx.1]
      · have : x = 1 := h
        linarith [hx.2]
    · linarith [h.2]
  have hax : a < x := lt_of_le_of_ne ha.2.2 (by intro h; exact hxZ (h ▸ ha.1))
  have hxb : x < b := lt_of_le_of_ne hb.2.1 (by intro h; exact hxZ (h.symm ▸ hb.1))
  have hendsa : a = 0 ∨ f a = c := by
    rcases ha.1 with h | h
    · rcases h with h | h
      · exact Or.inl h
      · have : a = 1 := h
        linarith [hx.2]
    · exact Or.inr h.2
  have hendsb : b = 1 ∨ f b = c := by
    rcases hb.1 with h | h
    · rcases h with h | h
      · have : b = 0 := h
        linarith [hx.1]
      · exact Or.inl h
    · exact Or.inr h.2
  have hpos : ∀ y ∈ Ioo a b, c < f y := by
    intro y hy
    by_contra h
    have hfy : f y ≤ c := le_of_not_gt h
    rcases le_total y x with hyx | hxy
    · obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hyx
        (hf.continuousOn.mono (fun z hz =>
          ⟨ha.2.1.trans (hy.1.le.trans hz.1), hz.2.trans hx.2.le⟩)) ⟨hfy, hfx.le⟩
      have hza : z ≤ a := hamax ⟨Or.inr ⟨⟨ha.2.1.trans (hy.1.le.trans hz.1),
        hz.2.trans hx.2.le⟩, hfz⟩, ha.2.1.trans (hy.1.le.trans hz.1), hz.2⟩
      linarith [hy.1, hz.1]
    · obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hxy
        (hf.continuousOn.mono (fun z hz =>
          ⟨hx.1.le.trans hz.1, hz.2.trans (hy.2.le.trans hb.2.2)⟩)) ⟨hfy, hfx.le⟩
      have hbz : b ≤ z := hbmin ⟨Or.inr ⟨⟨hx.1.le.trans hz.1,
        hz.2.trans (hy.2.le.trans hb.2.2)⟩, hfz⟩, hz.1, hz.2.trans (hy.2.le.trans hb.2.2)⟩
      linarith [hy.2, hz.2]
  have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' Ici c) :=
    hf.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcl : Icc a b ⊆ Icc (0 : ℝ) 1 ∩ f ⁻¹' Ici c := by
    rw [← closure_Ioo (hax.trans hxb).ne]
    apply closure_minimal _ hclosed
    intro y hy
    exact ⟨⟨ha.2.1.trans hy.1.le, hy.2.le.trans hb.2.2⟩, (hpos y hy).le⟩
  exact ⟨a, b, ha.2.1, hax, hxb, hb.2.2, hendsa, hendsb,
    (hcl ⟨le_rfl, (hax.trans hxb).le⟩).2,
    (hcl ⟨(hax.trans hxb).le, le_rfl⟩).2, hpos⟩

theorem regular_superlevel_subset_closure_positive_interior {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c : ℝ}
    (h0 : f 0 ≠ c) (h1 : f 1 ≠ c)
    (hreg : ∀ x ∈ Icc (0 : ℝ) 1, f x = c →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, f y - c = m * (y - x)) :
    {x ∈ Icc (0 : ℝ) 1 | c ≤ f x} ⊆ closure {x ∈ Ioo (0 : ℝ) 1 | c < f x} := by
  let g : ℝ → ℝ := fun x => f (projIcc (0 : ℝ) 1 zero_le_one x)
  have hgc : Continuous g := hf.continuousOn.domRestrict.comp continuous_projIcc
  have hgv {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : g x = f x := by
    dsimp [g]
    rw [projIcc_of_mem zero_le_one hx]
  intro x hx
  rcases hx.2.eq_or_lt with hfx | hfx
  · have hfx := hfx.symm
    have hx0 : 0 < x := lt_of_le_of_ne hx.1.1 (by intro h; exact h0 (h.symm ▸ hfx))
    have hx1 : x < 1 := lt_of_le_of_ne hx.1.2 (by intro h; exact h1 (h ▸ hfx))
    obtain ⟨u, v, m, hux, hxv, hm, hformula⟩ := hreg x hx.1 hfx
    rcases lt_or_gt_of_ne hm with hm | hm
    · have hu : max u 0 < x := max_lt hux hx0
      apply closure_mono (s := Ioo (max u 0) x) ?_ (by
        rw [closure_Ioo hu.ne]
        exact ⟨hu.le, le_rfl⟩)
      intro y hy
      have hyu := (le_max_left u 0).trans_lt hy.1
      have hfy := hformula y ⟨hyu.le, hy.2.le.trans hxv.le⟩
      refine ⟨⟨(le_max_right u 0).trans_lt hy.1, hy.2.trans hx1⟩, ?_⟩
      have := mul_pos_of_neg_of_neg hm (sub_neg.mpr hy.2)
      linarith
    · have hv : x < min v 1 := lt_min hxv hx1
      apply closure_mono (s := Ioo x (min v 1)) ?_ (by
        rw [closure_Ioo hv.ne]
        exact ⟨le_rfl, hv.le⟩)
      intro y hy
      have hyv := hy.2.trans_le (min_le_left v 1)
      have hfy := hformula y ⟨hux.le.trans hy.1.le, hyv.le⟩
      refine ⟨⟨hx0.trans hy.1, hy.2.trans_le (min_le_right v 1)⟩, ?_⟩
      have := mul_pos hm (sub_pos.mpr hy.1)
      linarith
  · have hopen : IsOpen {y | c < g y} := isOpen_lt continuous_const hgc
    have hxcl : x ∈ closure (Ioo (0 : ℝ) 1) ∩ {y | c < g y} := by
      rw [closure_Ioo zero_ne_one]
      exact ⟨hx.1, by change c < g x; rwa [hgv hx.1]⟩
    apply closure_mono (s := Ioo (0 : ℝ) 1 ∩ {y | c < g y}) ?_
      (hopen.closure_inter hxcl)
    intro y hy
    exact ⟨hy.1, hgv (Ioo_subset_Icc_self hy.1) ▸ hy.2⟩

theorem maximal_positive_intervals_disjoint {f : ℝ → ℝ} {c : ℝ}
    (hreg : ∀ x ∈ Icc (0 : ℝ) 1, f x = c →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, f y - c = m * (y - x))
    {a b d e : ℝ} (hab : a < b) (hde : d < e)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hd0 : 0 ≤ d) (he1 : e ≤ 1)
    (hfa : a = 0 ∨ f a = c) (hfb : b = 1 ∨ f b = c)
    (hfd : d = 0 ∨ f d = c) (hfe : e = 1 ∨ f e = c)
    (hpos : ∀ y ∈ Ioo a b, c < f y) (hpos' : ∀ y ∈ Ioo d e, c < f y)
    (hne : (a, b) ≠ (d, e)) : Disjoint (Icc a b) (Icc d e) := by
  have hordered {a b d e : ℝ} (hab : a < b) (hde : d < e)
      (ha : 0 ≤ a) (hb : b ≤ 1) (hfd : d = 0 ∨ f d = c)
      (hpos : ∀ y ∈ Ioo a b, c < f y) (hpos' : ∀ y ∈ Ioo d e, c < f y)
      (had : a < d) : b < d := by
    have hfd : f d = c := hfd.resolve_left (by intro h; linarith)
    by_contra h
    have hdb : d ≤ b := le_of_not_gt h
    rcases hdb.eq_or_lt with hdb | hdb
    · subst d
      exact no_positive_regular_local_minimum hab hde hpos hpos'
        (hreg b ⟨ha.trans hab.le, hb⟩ hfd)
    · have := hpos d ⟨had, hdb⟩
      linarith
  rcases lt_trichotomy a d with had | had | hda
  · exact disjoint_left.mpr (fun x hx hy =>
      (not_le_of_gt (hordered hab hde ha0 hb1 hfd hpos hpos' had)) (hy.1.trans hx.2))
  · subst d
    have hbe : b = e := by
      rcases lt_trichotomy b e with hbe | hbe | heb
      · have hfb := hfb.resolve_left (by intro h; linarith)
        have := hpos' b ⟨hab, hbe⟩
        linarith
      · exact hbe
      · have hfe := hfe.resolve_left (by intro h; linarith)
        have := hpos e ⟨hde, heb⟩
        linarith
    exact (hne (Prod.ext rfl hbe)).elim
  · exact disjoint_left.mpr (fun x hx hy =>
      (not_le_of_gt (hordered hde hab hd0 he1 hfa hpos' hpos hda)) (hx.1.trans hy.2))

theorem exists_complete_positive_interval_family {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) {c : ℝ}
    (h0 : f 0 ≠ c) (h1 : f 1 ≠ c)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | f x = c}.Finite)
    (hreg : ∀ x ∈ Icc (0 : ℝ) 1, f x = c →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, f y - c = m * (y - x)) :
    ∃ J : Finset (ℝ × ℝ),
      (∀ p ∈ J, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ f p.1 = c) ∧ (p.2 = 1 ∨ f p.2 = c) ∧
        c ≤ f p.1 ∧ c ≤ f p.2 ∧ ∀ y ∈ Ioo p.1 p.2, c < f y) ∧
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (Icc p.1 p.2) (Icc q.1 q.2)) ∧
      {x ∈ Icc (0 : ℝ) 1 | c ≤ f x} = ⋃ p ∈ J, Icc p.1 p.2 := by
  classical
  let Z : Set ℝ := {0, 1} ∪ {x ∈ Icc (0 : ℝ) 1 | f x = c}
  have hZ : Z.Finite := (show ({0, 1} : Set ℝ).Finite by simp).union hfinite
  let P : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
    (p.1 = 0 ∨ f p.1 = c) ∧ (p.2 = 1 ∨ f p.2 = c) ∧
    c ≤ f p.1 ∧ c ≤ f p.2 ∧ ∀ y ∈ Ioo p.1 p.2, c < f y}
  have hP : P.Finite := (hZ.prod hZ).subset (by
    rintro p ⟨ha, hab, hb, hfa, hfb, _⟩
    constructor
    · rcases hfa with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨⟨ha, hab.le.trans hb⟩, h⟩
    · rcases hfb with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨⟨ha.trans hab.le, hb⟩, h⟩)
  let J := hP.toFinset
  have hJ (p : ℝ × ℝ) (hp : p ∈ J) : p ∈ P := hP.mem_toFinset.mp hp
  have hclosed : IsClosed (⋃ p ∈ J, Icc p.1 p.2) :=
    (J.isCompact_biUnion (fun _ _ => isCompact_Icc)).isClosed
  have hcover : {x ∈ Ioo (0 : ℝ) 1 | c < f x} ⊆ ⋃ p ∈ J, Icc p.1 p.2 := by
    rintro x ⟨hx, hfx⟩
    obtain ⟨a, b, ha, hax, hxb, hb, hfa, hfb, hpa, hpb, hpos⟩ :=
      exists_maximal_positive_interval hf hfinite hx hfx
    exact mem_iUnion₂.mpr ⟨(a, b), hP.mem_toFinset.mpr
      ⟨ha, hax.trans hxb, hb, hfa, hfb, hpa, hpb, hpos⟩, hax.le, hxb.le⟩
  refine ⟨J, hJ, ?_, ?_⟩
  · intro p hp q hq hne
    obtain ⟨ha, hab, hb, hfa, hfb, _, _, hpos⟩ := hJ p hp
    obtain ⟨hd, hde, he, hfd, hfe, _, _, hpos'⟩ := hJ q hq
    exact maximal_positive_intervals_disjoint hreg hab hde ha hb hd he
      hfa hfb hfd hfe hpos hpos' (by simpa only [Prod.mk.eta] using hne)
  · apply Subset.antisymm
    · exact (regular_superlevel_subset_closure_positive_interior hf h0 h1 hreg).trans
        (closure_minimal hcover hclosed)
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
      obtain ⟨ha, hab, hb, _, _, hpa, hpb, hpos⟩ := hJ p hp
      refine ⟨⟨ha.trans hxp.1, hxp.2.trans hb⟩, ?_⟩
      rcases hxp.1.eq_or_lt with h | h
      · simpa only [h] using hpa
      · rcases hxp.2.eq_or_lt with h' | h'
        · simpa only [h'] using hpb
        · exact (hpos x ⟨h, h'⟩).le

end PoincareConjecture.M76.Dehn
