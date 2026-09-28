import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryParameters














noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_embedded_inner_return_region
    {gamma : ℝ → AnnulusCoordinates} {a b T : ℝ}
    (hab : a < b) (hperiod : b - a < rampPeriod) (hT : 0 < T)
    (hg : Continuous gamma) (hi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 a)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 b)
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (intrinsicAnnulusBoundary 1 '' Icc a b ∪ gamma '' Icc 0 T)ᶜ ∧
      frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ gamma '' Icc 0 T ∧
      frontier V = intrinsicAnnulusBoundary 1 '' Icc a b ∪ gamma '' Icc 0 T ∧
      IsCompact (closure U) := by
  let c : ℝ → AnnulusCoordinates :=
    fun x => intrinsicAnnulusBoundary 1 ((b - a) * x + a)
  let q : ℝ → AnnulusCoordinates := fun x => gamma (T * x)
  have hparam (x : ℝ) (hx : x ∈ Icc 0 1) : (b - a) * x + a ∈ Icc a b :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have htparam (x : ℝ) (hx : x ∈ Icc 0 1) : T * x ∈ Icc 0 T :=
    ⟨mul_nonneg hT.le hx.1, by nlinarith [hx.2]⟩
  have hc : ContinuousOn c (Icc 0 1) :=
    ((m64Intrinsic_contDiff_boundary 1).continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  have hci : InjOn c (Icc 0 1) := by
    intro x hx y hy hxy
    have h := m64Intrinsic_boundary_injOn_short_arc hperiod
      (hparam x hx) (hparam y hy) hxy
    nlinarith
  have hq : ContinuousOn q (Icc 0 1) :=
    (hg.comp (continuous_const.mul continuous_id)).continuousOn
  have hqi : InjOn q (Icc 0 1) := by
    intro x hx y hy hxy
    exact mul_left_cancel₀ hT.ne' (hi (htparam x hx) (htparam y hy) hxy)
  have hc0 : c 0 = q 0 := by simpa only [c, q, mul_zero, zero_add] using h0.symm
  have hc1 : c 1 = q 1 := by
    simpa only [c, q, mul_one, sub_add_cancel] using h1.symm
  have hmeet : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 1,
      c x = q y → (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
    intro x hx y hy heq
    by_cases hy0 : y = 0
    · subst y
      exact Or.inl ⟨hci hx (by norm_num) (heq.trans hc0.symm), rfl⟩
    by_cases hy1 : y = 1
    · subst y
      exact Or.inr ⟨hci hx (by norm_num) (heq.trans hc1.symm), rfl⟩
    have hnorm := hinside (T * y)
      ⟨mul_pos hT (lt_of_le_of_ne hy.1 (Ne.symm hy0)),
        mul_lt_of_lt_one_right hT (lt_of_le_of_ne hy.2 hy1)⟩
    change 1 < ‖q y‖ at hnorm
    rw [← heq] at hnorm
    exact False.elim ((lt_irrefl (1 : ℝ))
      (by simpa only [c, m64Intrinsic_inner_boundary_norm] using hnorm))
  have hcimage : c '' Icc 0 1 = intrinsicAnnulusBoundary 1 '' Icc a b := by
    change (intrinsicAnnulusBoundary 1 ∘ fun x => (b - a) * x + a) '' Icc 0 1 = _
    rw [image_comp, image_affine_Icc' (sub_pos.mpr hab)]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  have hqimage : q '' Icc 0 1 = gamma '' Icc 0 T := by
    change (gamma ∘ fun x => T * x) '' Icc 0 1 = _
    rw [image_comp, image_mul_left_Icc' hT]
    simp only [mul_zero, mul_one]
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd, hcover, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_region_between_arcs hc hq hci hqi hc0 hc1 hmeet
  rw [hcimage, hqimage] at hcover hfU hfV
  exact ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd, hcover, hfU, hfV, hcompact⟩






theorem m64Intrinsic_regular_inner_return_jordan
    {gamma : ℝ → AnnulusCoordinates} {a T : ℝ}
    (ha : a ∈ Ico (0 : ℝ) rampPeriod) (hT : 0 < T)
    (hg : ContDiff ℝ ∞ gamma)
    (hregular : ∀ t ∈ Icc 0 T, deriv gamma t ≠ 0)
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 a)
    (h1 : ‖gamma T‖ = 1)
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (frontier U)ᶜ ∧ frontier V = frontier U ∧
      IsCompact (closure U) ∧
      frontier U ⊆ intrinsicAnnulusBoundary 1 '' Icc 0 rampPeriod ∪ gamma '' Icc 0 T ∧
      (closure U ⊆ standardAnnulusDomain ∨ Metric.ball (0 : AnnulusCoordinates) 1 ⊆ U) := by
  let trace : Set AnnulusCoordinates :=
    intrinsicAnnulusBoundary 1 '' Icc 0 rampPeriod ∪ gamma '' Icc 0 T
  have htrace : trace ⊆ standardAnnulusDomain := by
    rintro p (⟨x, _, rfl⟩ | ⟨t, ht, rfl⟩)
    · change 1 ≤ ‖intrinsicAnnulusBoundary 1 x‖ ∧ ‖intrinsicAnnulusBoundary 1 x‖ ≤ 2
      rw [m64Intrinsic_inner_boundary_norm]
      norm_num
    · by_cases ht0 : t = 0
      · subst t
        change 1 ≤ ‖gamma 0‖ ∧ ‖gamma 0‖ ≤ 2
        rw [h0, m64Intrinsic_inner_boundary_norm]
        norm_num
      by_cases htT : t = T
      · subst t
        change 1 ≤ ‖gamma T‖ ∧ ‖gamma T‖ ≤ 2
        rw [h1]
        norm_num
      have h := hinside t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 htT⟩
      exact ⟨h.1.le, h.2.le⟩
  have finish (C U V : Set AnnulusCoordinates)
      (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
      (hcover : U ∪ V = Cᶜ) (hfU : frontier U = C)
      (hcompact : IsCompact (closure U)) (hsub : C ⊆ trace) :
      IsCompact (closure U) ∧ frontier U ⊆ trace ∧
        (closure U ⊆ standardAnnulusDomain ∨ Metric.ball (0 : AnnulusCoordinates) 1 ⊆ U) :=
    ⟨hcompact, by simpa only [hfU] using hsub,
      m64Intrinsic_jordan_annulus_dichotomy hU hV hd hcover hfU hcompact
        (hsub.trans htrace)⟩
  by_cases hi : InjOn gamma (Icc 0 T)
  · obtain ⟨b, hb, hbpoint⟩ := m64Intrinsic_exists_boundary_parameter h1
    have habne : a ≠ b := by
      intro hab
      have heq := hi (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
        (show T ∈ Icc 0 T from ⟨hT.le, le_rfl⟩)
        (h0.trans (by simpa only [hab] using hbpoint.symm))
      exact hT.ne' heq.symm
    rcases lt_or_gt_of_ne habne with hab | hba
    · obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd, hcover, hfU, hfV, hcompact⟩ :=
        m64Intrinsic_embedded_inner_return_region hab (by linarith [ha.1, hb.2]) hT
          hg.continuous hi h0 hbpoint (fun t ht => (hinside t ht).1)
      refine ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd,
        by simpa only [hfU] using hcover, hfV.trans hfU.symm, ?_⟩
      apply finish _ U V hU hV hd hcover hfU hcompact
      exact union_subset_union_left _ (image_mono (Icc_subset_Icc ha.1 hb.2.le))
    · let rev : ℝ → AnnulusCoordinates := fun t => gamma (T - t)
      have hrev : Continuous rev := hg.continuous.comp (continuous_const.sub continuous_id)
      have hrevi : InjOn rev (Icc 0 T) := by
        intro s hs t ht heq
        have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
          ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
        linarith
      have hrev0 : rev 0 = intrinsicAnnulusBoundary 1 b := by
        simpa only [rev, sub_zero] using hbpoint
      have hrevT : rev T = intrinsicAnnulusBoundary 1 a := by
        simpa only [rev, sub_self] using h0
      have hrevInside : ∀ t ∈ Ioo 0 T, 1 < ‖rev t‖ := by
        intro t ht
        exact (hinside (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).1
      have hrevImage : rev '' Icc 0 T = gamma '' Icc 0 T := by
        change (gamma ∘ fun t => T - t) '' Icc 0 T = _
        rw [image_comp, image_const_sub_Icc]
        simp only [sub_self, sub_zero]
      obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd, hcover, hfU, hfV, hcompact⟩ :=
        m64Intrinsic_embedded_inner_return_region hba (by linarith [hb.1, ha.2]) hT
          hrev hrevi hrev0 hrevT hrevInside
      rw [hrevImage] at hcover hfU hfV
      refine ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd,
        by simpa only [hfU] using hcover, hfV.trans hfU.symm, ?_⟩
      apply finish _ U V hU hV hd hcover hfU hcompact
      exact union_subset_union_left _ (image_mono (Icc_subset_Icc hb.1 ha.2.le))
  · obtain ⟨s, t, hs, hst, htT, _, _, U, V, hU, hV, hpU, hpV, hbU, hbV,
        hd, hcover, hfU, hfV, hcompact⟩ :=
      m64Intrinsic_regular_selfintersection_region hg hregular hi
    refine ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd,
      by simpa only [hfU] using hcover, hfV.trans hfU.symm, ?_⟩
    apply finish _ U V hU hV hd hcover hfU hcompact
    exact (image_mono (Icc_subset_Icc hs htT)).trans subset_union_right

end PoincareConjecture
