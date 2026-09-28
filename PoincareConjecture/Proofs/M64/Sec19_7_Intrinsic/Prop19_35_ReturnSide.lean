import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionConfinement














noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture




theorem m64Intrinsic_first_return_prefix_disjoint
    {gamma : ℝ → AnnulusCoordinates} {a s t : ℝ}
    (has : a ≤ s) (hst : s < t) (hend : gamma s = gamma t)
    (hinj : InjOn gamma (Ico a t)) :
    Disjoint (gamma '' Ico a s) (gamma '' Icc s t) := by
  apply disjoint_left.mpr
  rintro p ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have hxI : x ∈ Ico a t := ⟨hx.1, hx.2.trans hst⟩
  have heq : gamma x = gamma y := hxq.trans hyq.symm
  rcases eq_or_lt_of_le hy.2 with hyend | hylt
  · have hxs := hinj hxI ⟨has, hst⟩ (heq.trans (hyend ▸ hend.symm))
    exact hx.2.ne hxs
  · have hxy := hinj hxI ⟨has.trans hy.1, hylt⟩ heq
    linarith [hx.2, hy.1]




theorem m64Intrinsic_first_return_prefix_side
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {a s t : ℝ}
    (has : a ≤ s) (hst : s < t) (hend : gamma s = gamma t)
    (hinj : InjOn gamma (Ico a t))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = (gamma '' Icc s t)ᶜ) :
    gamma '' Ico a s ⊆ U ∨ gamma '' Ico a s ⊆ V := by
  apply (isPreconnected_Ico.image gamma hg.continuousOn).subset_or_subset hU hV hdisj
  rw [hcover]
  exact (m64Intrinsic_first_return_prefix_disjoint has hst hend hinj).subset_compl_right





theorem m64Intrinsic_internal_return_trace
    {gamma : ℝ → AnnulusCoordinates} {s t height : ℝ}
    (hs : 0 < s) (hst : s < t) (hth : t ≤ height) (hend : gamma s = gamma t)
    (hinside : ∀ x ∈ Ioo (0 : ℝ) height, 1 < ‖gamma x‖ ∧ ‖gamma x‖ < 2) :
    ∀ p ∈ gamma '' Icc s t, 1 < ‖p‖ ∧ ‖p‖ < 2 := by
  rintro p ⟨x, hx, rfl⟩
  rcases eq_or_lt_of_le hx.2 with heq | hlt
  · rw [heq, ← hend]
    exact hinside s ⟨hs, hst.trans_le hth⟩
  · exact hinside x ⟨hs.trans_le hx.1, hlt.trans_le hth⟩






theorem m64Intrinsic_jordan_annulus_dichotomy
    {C U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = Cᶜ)
    (hfront : frontier U = C) (hcompact : IsCompact (closure U))
    (htrace : C ⊆ standardAnnulusDomain) :
    closure U ⊆ standardAnnulusDomain ∨ ball (0 : AnnulusCoordinates) 1 ⊆ U := by
  have hball : ball (0 : AnnulusCoordinates) 1 ⊆ U ∪ V := by
    rw [hcover]
    intro x hx hC
    have hxnorm : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    exact not_lt_of_ge (htrace hC).1 hxnorm
  rcases (convex_ball (0 : AnnulusCoordinates) (1 : ℝ)).isPreconnected.subset_or_subset
      hU hV hdisj hball with hleft | hright
  · exact Or.inr hleft
  · apply Or.inl
    apply m64Intrinsic_jordan_closure_subset_annulus hcompact ?_ (hfront ▸ htrace)
    have hzV : (0 : AnnulusCoordinates) ∈ V := hright (mem_ball_self zero_lt_one)
    intro hzU
    obtain ⟨x, hxV, hxU⟩ := mem_closure_iff.mp hzU V hV hzV
    exact disjoint_left.mp hdisj hxU hxV






theorem m64Intrinsic_return_region_annulus_dichotomy
    {C U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = Cᶜ)
    (hfront : frontier U = C) (hcompact : IsCompact (closure U))
    (htrace : ∀ p ∈ C, 1 < ‖p‖ ∧ ‖p‖ ≤ 2) :
    closure U ⊆ standardAnnulusDomain ∨ closedBall (0 : AnnulusCoordinates) 1 ⊆ U := by
  have hball : closedBall (0 : AnnulusCoordinates) 1 ⊆ U ∪ V := by
    rw [hcover]
    intro x hx hC
    have hxnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    exact not_lt_of_ge hxnorm (htrace x hC).1
  rcases (convex_closedBall (0 : AnnulusCoordinates) (1 : ℝ)).isPreconnected.subset_or_subset
      hU hV hdisj hball with hleft | hright
  · exact Or.inr hleft
  · apply Or.inl
    apply m64Intrinsic_jordan_closure_subset_annulus hcompact ?_ ?_
    · have hzV : (0 : AnnulusCoordinates) ∈ V := hright (mem_closedBall_self zero_le_one)
      intro hzU
      obtain ⟨x, hxV, hxU⟩ := mem_closure_iff.mp hzU V hV hzV
      exact disjoint_left.mp hdisj hxU hxV
    · rw [hfront]
      intro p hp
      exact ⟨(htrace p hp).1.le, (htrace p hp).2⟩

end PoincareConjecture
