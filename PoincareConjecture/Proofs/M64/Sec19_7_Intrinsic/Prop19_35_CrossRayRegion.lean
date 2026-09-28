import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcRegion

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_first_crossing
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ}
    (ha : Continuous alpha) (hb : Continuous beta)
    (ha0 : alpha 0 ∉ beta '' Icc 0 B) (hb0 : beta 0 ∉ alpha '' Icc 0 A)
    (hmeet : ∃ s ∈ Icc 0 A, ∃ t ∈ Icc 0 B, alpha s = beta t) :
    ∃ s t : ℝ, 0 < s ∧ s ≤ A ∧ 0 < t ∧ t ≤ B ∧ alpha s = beta t ∧
      ∀ x ∈ Icc 0 s, ∀ y ∈ Icc 0 t,
        alpha x = beta y → x = s ∧ y = t := by
  let C : Set (ℝ × ℝ) := (Icc 0 A ×ˢ Icc 0 B) ∩
    {p | alpha p.1 = beta p.2}
  have hC : IsCompact C :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_eq (ha.comp continuous_fst) (hb.comp continuous_snd))
  obtain ⟨s, hs, t, ht, hst⟩ := hmeet
  have hCne : C.Nonempty := ⟨(s, t), ⟨⟨hs, ht⟩, hst⟩⟩
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hCne
    (continuous_fst.add continuous_snd).continuousOn
  have hpEq : alpha p.1 = beta p.2 := hp.2
  have hp0 : 0 < p.1 := by
    apply lt_of_le_of_ne hp.1.1.1
    intro hzero
    apply ha0
    exact ⟨p.2, hp.1.2, by simpa only [← hzero] using hpEq.symm⟩
  have hp1 : 0 < p.2 := by
    apply lt_of_le_of_ne hp.1.2.1
    intro hzero
    apply hb0
    exact ⟨p.1, hp.1.1, by simpa only [← hzero] using hpEq⟩
  refine ⟨p.1, p.2, hp0, hp.1.1.2, hp1, hp.1.2.2, hp.2, ?_⟩
  intro x hx y hy hxy
  have hxyC : (x, y) ∈ C :=
    ⟨⟨⟨hx.1, hx.2.trans hp.1.1.2⟩, ⟨hy.1, hy.2.trans hp.1.2.2⟩⟩, hxy⟩
  have hsum := hmin hxyC
  change p.1 + p.2 ≤ x + y at hsum
  constructor <;> linarith [hx.2, hy.2]

theorem m64Intrinsic_exists_embedded_join
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContinuousOn alpha (Icc 0 1)) (hb : ContinuousOn beta (Icc 0 1))
    (hai : InjOn alpha (Icc 0 1)) (hbi : InjOn beta (Icc 0 1))
    (hend : alpha 1 = beta 0)
    (hmeet : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      alpha s = beta t → s = 1 ∧ t = 0) :
    ∃ gamma : ℝ → AnnulusCoordinates,
      ContinuousOn gamma (Icc 0 1) ∧ InjOn gamma (Icc 0 1) ∧
      gamma 0 = alpha 0 ∧ gamma 1 = beta 1 ∧
      gamma '' Icc 0 1 = alpha '' Icc 0 1 ∪ beta '' Icc 0 1 := by
  classical
  let gamma : ℝ → AnnulusCoordinates :=
    fun t => if t ≤ 1 / 2 then alpha (2 * t) else beta (2 * t - 1)
  have hgc : ContinuousOn gamma (Icc 0 1) := by
    apply ContinuousOn.if
    · intro t ht
      have ht' : t = 1 / 2 := by
        have h := ht.2
        change t ∈ frontier (Iic (1 / 2 : ℝ)) at h
        simpa only [frontier_Iic, mem_singleton_iff] using h
      subst t
      simpa using hend
    · apply ha.comp (continuous_const.mul continuous_id).continuousOn
      intro t ht
      have ht' : t ≤ 1 / 2 := by
        have h := ht.2
        change t ∈ closure (Iic (1 / 2 : ℝ)) at h
        simpa only [isClosed_Iic.closure_eq, mem_Iic] using h
      change 2 * t ∈ Icc (0 : ℝ) 1
      exact ⟨by linarith [ht.1.1], by linarith⟩
    · apply hb.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
      intro t ht
      have ht' : 1 / 2 ≤ t := by
        have h := ht.2
        simp only [not_le] at h
        change t ∈ closure (Ioi (1 / 2 : ℝ)) at h
        simpa only [closure_Ioi, mem_Ici] using h
      change 2 * t - 1 ∈ Icc (0 : ℝ) 1
      exact ⟨by linarith, by linarith [ht.1.2]⟩
  have hgi : InjOn gamma (Icc 0 1) := by
    intro s hs t ht heq
    wlog hst : s ≤ t generalizing s t
    · exact (this ht hs heq.symm (le_of_not_ge hst)).symm
    by_cases ht2 : t ≤ 1 / 2
    · have hs2 := hst.trans ht2
      have h := hai (x₁ := 2 * s) (x₂ := 2 * t)
        ⟨by linarith [hs.1], by linarith⟩
        ⟨by linarith [ht.1], by linarith⟩
        (by simpa only [gamma, if_pos hs2, if_pos ht2] using heq)
      linarith
    · by_cases hs2 : s ≤ 1 / 2
      · have h := hmeet (2 * s) ⟨by linarith [hs.1], by linarith⟩
          (2 * t - 1) ⟨by linarith, by linarith [ht.2]⟩
          (by simpa only [gamma, if_pos hs2, if_neg ht2] using heq)
        linarith [h.2]
      · have h := hbi (x₁ := 2 * s - 1) (x₂ := 2 * t - 1)
          ⟨by linarith, by linarith [hs.2]⟩
          ⟨by linarith, by linarith [ht.2]⟩
          (by simpa only [gamma, if_neg hs2, if_neg ht2] using heq)
        linarith
  refine ⟨gamma, hgc, hgi, by norm_num [gamma], by norm_num [gamma], ?_⟩
  apply Subset.antisymm
  · rintro p ⟨t, ht, rfl⟩
    by_cases ht2 : t ≤ 1 / 2
    · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩,
        (if_pos ht2).symm⟩
    · exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩,
        (if_neg ht2).symm⟩
  · rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      simp only [gamma, if_pos (by linarith [ht.2] : t / 2 ≤ 1 / 2)]
      congr 1
      ring
    · refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      by_cases ht0 : t = 0
      · subst t
        simpa [gamma] using hend
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        simp only [gamma, if_neg (by linarith : ¬ (t + 1) / 2 ≤ 1 / 2)]
        congr 1
        ring

theorem m64Intrinsic_exists_crossing_ray_region
    {alpha beta base : ℝ → AnnulusCoordinates} {A B : ℝ}
    (ha : Continuous alpha) (hb : Continuous beta)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hc : ContinuousOn base (Icc 0 1)) (hci : InjOn base (Icc 0 1))
    (hstart : base 0 = alpha 0) (hend : base 1 = beta 0)
    (hca : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 A,
      base x = alpha t → x = 0 ∧ t = 0)
    (hcb : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 B,
      base x = beta t → x = 1 ∧ t = 0)
    (hmeet : ∃ s ∈ Icc 0 A, ∃ t ∈ Icc 0 B, alpha s = beta t) :
    ∃ s t : ℝ, 0 < s ∧ s ≤ A ∧ 0 < t ∧ t ≤ B ∧ alpha s = beta t ∧
      ∃ U V : Set AnnulusCoordinates,
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
        Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
        U ∪ V = (base '' Icc 0 1 ∪ (alpha '' Icc 0 s ∪ beta '' Icc 0 t))ᶜ ∧
        frontier U = base '' Icc 0 1 ∪ (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧
        frontier V = base '' Icc 0 1 ∪ (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧
        IsCompact (closure U) := by
  have ha0 : alpha 0 ∉ beta '' Icc 0 B := by
    rintro ⟨t, ht, heq⟩
    have h := (hcb 0 (by norm_num) t ht (hstart.trans heq.symm)).1
    norm_num at h
  have hb0 : beta 0 ∉ alpha '' Icc 0 A := by
    rintro ⟨s, hs, heq⟩
    have h := (hca 1 (by norm_num) s hs (hend.trans heq.symm)).1
    norm_num at h
  obtain ⟨s, t, hs, hsA, ht, htB, hst, hfirst⟩ :=
    m64Intrinsic_exists_first_crossing ha hb ha0 hb0 hmeet
  let f : ℝ → AnnulusCoordinates := fun x => alpha (s * x)
  let g : ℝ → AnnulusCoordinates := fun x => beta (t * (1 - x))
  have hsparam (x : ℝ) (hx : x ∈ Icc 0 1) : s * x ∈ Icc 0 s :=
    ⟨mul_nonneg hs.le hx.1, by nlinarith [hx.2]⟩
  have htparam (x : ℝ) (hx : x ∈ Icc 0 1) : t * (1 - x) ∈ Icc 0 t :=
    ⟨by nlinarith [hx.2], by nlinarith [hx.1]⟩
  have hf : ContinuousOn f (Icc 0 1) :=
    (ha.comp (continuous_const.mul continuous_id)).continuousOn
  have hg : ContinuousOn g (Icc 0 1) :=
    (hb.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hfi : InjOn f (Icc 0 1) := by
    intro x hx y hy hxy
    have h := hai ⟨(hsparam x hx).1, (hsparam x hx).2.trans hsA⟩
      ⟨(hsparam y hy).1, (hsparam y hy).2.trans hsA⟩ hxy
    exact mul_left_cancel₀ hs.ne' h
  have hgi : InjOn g (Icc 0 1) := by
    intro x hx y hy hxy
    have h := hbi ⟨(htparam x hx).1, (htparam x hx).2.trans htB⟩
      ⟨(htparam y hy).1, (htparam y hy).2.trans htB⟩ hxy
    nlinarith
  have hfg : f 1 = g 0 := by simpa only [f, g, mul_one, sub_zero] using hst
  have hfgmeet : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 1,
      f x = g y → x = 1 ∧ y = 0 := by
    intro x hx y hy hxy
    have h := hfirst (s * x) (hsparam x hx) (t * (1 - y)) (htparam y hy) hxy
    constructor <;> nlinarith [h.1, h.2]
  obtain ⟨q, hq, hqi, hq0, hq1, hqimage⟩ :=
    m64Intrinsic_exists_embedded_join hf hg hfi hgi hfg hfgmeet
  have hfimage : f '' Icc 0 1 = alpha '' Icc 0 s := by
    change (alpha ∘ fun x => s * x) '' Icc 0 1 = _
    rw [image_comp, image_mul_left_Icc' hs]
    simp only [mul_zero, mul_one]
  have hgimage : g '' Icc 0 1 = beta '' Icc 0 t := by
    change (beta ∘ (fun x => t * x) ∘ (fun x => 1 - x)) '' Icc 0 1 = _
    rw [image_comp, image_comp, image_const_sub_Icc]
    norm_num only [sub_self, sub_zero]
    rw [image_mul_left_Icc' ht]
    simp only [mul_zero, mul_one]
  have hq0' : q 0 = alpha 0 := by simpa only [f, mul_zero] using hq0
  have hq1' : q 1 = beta 0 := by simpa only [g, sub_self, mul_zero] using hq1
  have hbaseq : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 1,
      base x = q y → (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
    intro x hx y hy hxy
    have hyimage : q y ∈ f '' Icc 0 1 ∪ g '' Icc 0 1 :=
      hqimage ▸ mem_image_of_mem q hy
    rcases hyimage with ⟨z, hz, hzq⟩ | ⟨z, hz, hzq⟩
    · have h := hca x hx (s * z)
        ⟨(hsparam z hz).1, (hsparam z hz).2.trans hsA⟩ (hxy.trans hzq.symm)
      refine Or.inl ⟨h.1, hqi hy (by norm_num) ?_⟩
      rw [← hxy, h.1, hq0', hstart]
    · have h := hcb x hx (t * (1 - z))
        ⟨(htparam z hz).1, (htparam z hz).2.trans htB⟩ (hxy.trans hzq.symm)
      refine Or.inr ⟨h.1, hqi hy (by norm_num) ?_⟩
      rw [← hxy, h.1, hq1', hend]
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hcover, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_region_between_arcs hc hq hci hqi
      (hstart.trans hq0'.symm) (hend.trans hq1'.symm) hbaseq
  rw [hqimage, hfimage, hgimage] at hcover hfU hfV
  exact ⟨s, t, hs, hsA, ht, htB, hst, U, V, hU, hV, hpU, hpV, hbU, hbV,
    hdisj, hcover, hfU, hfV, hcompact⟩

end PoincareConjecture
