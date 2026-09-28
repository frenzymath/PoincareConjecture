import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_EmbeddedCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalReturnRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnSide














noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology ContDiff

namespace PoincareConjecture




theorem m64Intrinsic_inner_boundary_norm (x : ℝ) :
    ‖intrinsicAnnulusBoundary 1 x‖ = 1 := by
  have h := m64Intrinsic_boundary_self_inner 1 x
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 x)]






theorem m64Intrinsic_inward_crossing_region
    {alpha beta : ℝ → AnnulusCoordinates} {a b A B : ℝ}
    (hab : a < b) (hperiod : b - a < rampPeriod)
    (ha : Continuous alpha) (hb : Continuous beta)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b)
    (haInterior : ∀ s ∈ Ioc 0 A, 1 < ‖alpha s‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hmeet : ∃ s ∈ Icc 0 A, ∃ t ∈ Icc 0 B, alpha s = beta t) :
    ∃ s t : ℝ, 0 < s ∧ s ≤ A ∧ 0 < t ∧ t ≤ B ∧ alpha s = beta t ∧
      ∃ U V : Set AnnulusCoordinates,
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
        Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
        U ∪ V = (intrinsicAnnulusBoundary 1 '' Icc a b ∪
          (alpha '' Icc 0 s ∪ beta '' Icc 0 t))ᶜ ∧
        frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
          (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧
        frontier V = intrinsicAnnulusBoundary 1 '' Icc a b ∪
          (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧ IsCompact (closure U) := by
  let c : ℝ → AnnulusCoordinates :=
    fun x => intrinsicAnnulusBoundary 1 ((b - a) * x + a)
  have hparam (x : ℝ) (hx : x ∈ Icc 0 1) : (b - a) * x + a ∈ Icc a b :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have hc : ContinuousOn c (Icc 0 1) :=
    ((m64Intrinsic_contDiff_boundary 1).continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  have hci : InjOn c (Icc 0 1) := by
    intro x hx y hy hxy
    have h := m64Intrinsic_boundary_injOn_short_arc hperiod
      (hparam x hx) (hparam y hy) hxy
    nlinarith
  have hc0 : c 0 = alpha 0 := by simpa only [c, mul_zero, zero_add] using ha0.symm
  have hc1 : c 1 = beta 0 := by simpa only [c, mul_one, sub_add_cancel] using hb0.symm
  have hca : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 A,
      c x = alpha t → x = 0 ∧ t = 0 := by
    intro x hx t ht heq
    have ht0 : t = 0 := by
      by_contra hne
      have hnorm := haInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hne), ht.2⟩
      rw [← heq] at hnorm
      exact (lt_irrefl (1 : ℝ))
        (by simpa only [c, m64Intrinsic_inner_boundary_norm] using hnorm)
    refine ⟨hci hx (by norm_num) ?_, ht0⟩
    rw [heq, ht0, hc0]
  have hcb : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 B,
      c x = beta t → x = 1 ∧ t = 0 := by
    intro x hx t ht heq
    have ht0 : t = 0 := by
      by_contra hne
      have hnorm := hbInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hne), ht.2⟩
      rw [← heq] at hnorm
      exact (lt_irrefl (1 : ℝ))
        (by simpa only [c, m64Intrinsic_inner_boundary_norm] using hnorm)
    refine ⟨hci hx (by norm_num) ?_, ht0⟩
    rw [heq, ht0, hc1]
  have hcimage : c '' Icc 0 1 = intrinsicAnnulusBoundary 1 '' Icc a b := by
    change (intrinsicAnnulusBoundary 1 ∘ fun x => (b - a) * x + a) '' Icc 0 1 = _
    rw [image_comp, image_affine_Icc' (sub_pos.mpr hab)]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  obtain ⟨s, t, hs, hsA, ht, htB, hst, U, V, hU, hV, hpU, hpV, hbU, hbV,
      hdisj, hcover, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_crossing_ray_region ha hb hai hbi hc hci hc0 hc1 hca hcb hmeet
  rw [hcimage] at hcover hfU hfV
  exact ⟨s, t, hs, hsA, ht, htB, hst, U, V, hU, hV, hpU, hpV, hbU, hbV,
    hdisj, hcover, hfU, hfV, hcompact⟩







theorem m64Intrinsic_regular_inward_collision_jordan
    {alpha beta : ℝ → AnnulusCoordinates} {a b A B : ℝ}
    (hab : a < b) (hperiod : b - a < rampPeriod)
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (haRegular : ∀ s ∈ Icc 0 A, deriv alpha s ≠ 0)
    (hbRegular : ∀ t ∈ Icc 0 B, deriv beta t ≠ 0)
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b)
    (haInterior : ∀ s ∈ Ioc 0 A, 1 < ‖alpha s‖ ∧ ‖alpha s‖ ≤ 2)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖ ∧ ‖beta t‖ ≤ 2)
    (hmeet : ∃ s ∈ Icc 0 A, ∃ t ∈ Icc 0 B, alpha s = beta t) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (frontier U)ᶜ ∧ frontier V = frontier U ∧
      IsCompact (closure U) ∧
      frontier U ⊆ intrinsicAnnulusBoundary 1 '' Icc a b ∪
        (alpha '' Icc 0 A ∪ beta '' Icc 0 B) ∧
      (closure U ⊆ standardAnnulusDomain ∨ Metric.ball (0 : AnnulusCoordinates) 1 ⊆ U) := by
  let trace : Set AnnulusCoordinates := intrinsicAnnulusBoundary 1 '' Icc a b ∪
    (alpha '' Icc 0 A ∪ beta '' Icc 0 B)
  have htrace : trace ⊆ standardAnnulusDomain := by
    rintro p (⟨x, _, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · change 1 ≤ ‖intrinsicAnnulusBoundary 1 x‖ ∧ ‖intrinsicAnnulusBoundary 1 x‖ ≤ 2
      rw [m64Intrinsic_inner_boundary_norm]
      norm_num
    · by_cases hs0 : s = 0
      · subst s
        change 1 ≤ ‖alpha 0‖ ∧ ‖alpha 0‖ ≤ 2
        rw [ha0, m64Intrinsic_inner_boundary_norm]
        norm_num
      · have h := haInterior s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
        exact ⟨h.1.le, h.2⟩
    · by_cases ht0 : t = 0
      · subst t
        change 1 ≤ ‖beta 0‖ ∧ ‖beta 0‖ ≤ 2
        rw [hb0, m64Intrinsic_inner_boundary_norm]
        norm_num
      · have h := hbInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        exact ⟨h.1.le, h.2⟩
  have finish (C U V : Set AnnulusCoordinates)
      (hU : IsOpen U) (hV : IsOpen V)
      (hdisj : Disjoint U V) (hcover : U ∪ V = Cᶜ)
      (hfU : frontier U = C) (hfV : frontier V = C)
      (hcompact : IsCompact (closure U)) (hsub : C ⊆ trace) :
      IsCompact (closure U) ∧ frontier U ⊆ trace ∧
        (closure U ⊆ standardAnnulusDomain ∨ Metric.ball (0 : AnnulusCoordinates) 1 ⊆ U) := by
    refine ⟨hcompact, by simpa only [hfU] using hsub, ?_⟩
    exact m64Intrinsic_jordan_annulus_dichotomy hU hV hdisj hcover hfU hcompact
      (hsub.trans htrace)
  by_cases hai : InjOn alpha (Icc 0 A)
  · by_cases hbi : InjOn beta (Icc 0 B)
    · obtain ⟨s, t, hs, hsA, ht, htB, _, U, V, hU, hV, hpU, hpV, hbU, hbV,
          hdisj, hcover, hfU, hfV, hcompact⟩ :=
        m64Intrinsic_inward_crossing_region hab hperiod ha.continuous hb.continuous
          hai hbi ha0 hb0 (fun s hs => (haInterior s hs).1)
          (fun t ht => (hbInterior t ht).1) hmeet
      refine ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj,
        by simpa only [hfU] using hcover, hfV.trans hfU.symm, ?_⟩
      apply finish _ U V hU hV hdisj hcover hfU hfV hcompact
      exact union_subset_union_right _ (union_subset_union
        (image_mono (Icc_subset_Icc_right hsA)) (image_mono (Icc_subset_Icc_right htB)))
    · obtain ⟨s, t, hs, hst, htB, _, _, U, V, hU, hV, hpU, hpV, hbU, hbV,
          hdisj, hcover, hfU, hfV, hcompact⟩ :=
        m64Intrinsic_regular_selfintersection_region hb hbRegular hbi
      refine ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj,
        by simpa only [hfU] using hcover, hfV.trans hfU.symm, ?_⟩
      apply finish _ U V hU hV hdisj hcover hfU hfV hcompact
      exact (image_mono (Icc_subset_Icc hs htB)).trans
        (subset_union_of_subset_right (subset_union_right) _)
  · obtain ⟨s, t, hs, hst, htA, _, _, U, V, hU, hV, hpU, hpV, hbU, hbV,
        hdisj, hcover, hfU, hfV, hcompact⟩ :=
      m64Intrinsic_regular_selfintersection_region ha haRegular hai
    refine ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj,
      by simpa only [hfU] using hcover, hfV.trans hfU.symm, ?_⟩
    apply finish _ U V hU hV hdisj hcover hfU hfV hcompact
    exact (image_mono (Icc_subset_Icc hs htA)).trans
      (subset_union_of_subset_right (subset_union_left) _)






theorem m64Intrinsic_normal_interior_collision_jordan
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    (hboundary : ∀ x, u (x, 0) = intrinsicAnnulusBoundary 1 x)
    {a b A B : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hai : ∀ s ∈ Icc 0 A, Function.Injective (fderiv ℝ u (a, s)))
    (hbi : ∀ t ∈ Icc 0 B, Function.Injective (fderiv ℝ u (b, t)))
    (haInterior : ∀ s ∈ Ioc 0 A, 1 < ‖u (a, s)‖ ∧ ‖u (a, s)‖ ≤ 2)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖u (b, t)‖ ∧ ‖u (b, t)‖ ≤ 2)
    (hmeet : ∃ s ∈ Icc 0 A, ∃ t ∈ Icc 0 B, u (a, s) = u (b, t)) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (frontier U)ᶜ ∧ frontier V = frontier U ∧
      IsCompact (closure U) ∧
      frontier U ⊆ intrinsicAnnulusBoundary 1 '' Icc a b ∪
        ((fun s => u (a, s)) '' Icc 0 A ∪ (fun t => u (b, t)) '' Icc 0 B) ∧
      (closure U ⊆ standardAnnulusDomain ∨ Metric.ball (0 : AnnulusCoordinates) 1 ⊆ U) := by
  have hregular (x T : ℝ)
      (hi : ∀ s ∈ Icc 0 T, Function.Injective (fderiv ℝ u (x, s))) :
      ∀ s ∈ Icc 0 T, deriv (fun t => u (x, t)) s ≠ 0 := by
    intro s hs hzero
    rw [m64Intrinsic_normal_ray_deriv (hu.differentiable (by simp) (x, s))] at hzero
    have h := hi s hs (hzero.trans (fderiv ℝ u (x, s)).map_zero.symm)
    have hlast := congrArg Prod.snd h
    norm_num at hlast
  exact m64Intrinsic_regular_inward_collision_jordan hab hperiod
    (hu.comp (by fun_prop)) (hu.comp (by fun_prop))
    (hregular a A hai) (hregular b B hbi)
    (hboundary a) (hboundary b) haInterior hbInterior hmeet

end PoincareConjecture
