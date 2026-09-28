import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedReturnRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease











noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture






theorem m64Intrinsic_exists_central_return_child
    (N : IntrinsicAnnulus)
    {U V : Set AnnulusCoordinates}
    (hU : IsOpen U) (hV : IsOpen V) (hpV : IsPreconnected V)
    (hbV : ¬ Bornology.IsBounded V) (hd : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b z w T epsilon : ℝ}
    (hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U)
    (hperiod : b - a < rampPeriod)
    (hz : z ∈ Icc a b) (hw : w ∈ Icc a b) (hT : 0 < T)
    {gamma : ℝ → AnnulusCoordinates}
    (hg : Continuous gamma) (hi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 z)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 w)
    (hprefix : ∀ t ∈ Ioo 0 T, gamma t ∈ U)
    (hleft : epsilon ≤ intrinsicBoundaryLength N.metric 1 a z)
    (hright : epsilon ≤ intrinsicBoundaryLength N.metric 1 z b) :
    ∃ U' V' : Set AnnulusCoordinates,
      IsOpen U' ∧ IsOpen V' ∧ IsPathConnected U' ∧ IsPathConnected V' ∧
      Bornology.IsBounded U' ∧ ¬ Bornology.IsBounded V' ∧ Disjoint U' V' ∧
      U' ∪ V' =
        (intrinsicAnnulusBoundary 1 '' Icc (min z w) (max z w) ∪ gamma '' Icc 0 T)ᶜ ∧
      frontier U' =
        intrinsicAnnulusBoundary 1 '' Icc (min z w) (max z w) ∪ gamma '' Icc 0 T ∧
      frontier V' =
        intrinsicAnnulusBoundary 1 '' Icc (min z w) (max z w) ∪ gamma '' Icc 0 T ∧
      IsCompact (closure U') ∧ U' ⊆ U ∧ closure U' ⊆ closure U ∧
      closure U' ⊆ standardAnnulusDomain ∧
      intrinsicBoundaryLength N.metric 1 (min z w) (max z w) ≤
        intrinsicBoundaryLength N.metric 1 a b - epsilon := by
  have hzw : z ≠ w := by
    intro heq
    have hpoints : gamma 0 = gamma T := by rw [h0, h1, heq]
    exact hT.ne (hi ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hpoints)
  have hends :
      (gamma 0 = intrinsicAnnulusBoundary 1 (min z w) ∧
        gamma T = intrinsicAnnulusBoundary 1 (max z w)) ∨
      (gamma 0 = intrinsicAnnulusBoundary 1 (max z w) ∧
        gamma T = intrinsicAnnulusBoundary 1 (min z w)) := by
    rcases le_total z w with h | h
    · exact Or.inl (by simpa only [min_eq_left h, max_eq_right h] using And.intro h0 h1)
    · exact Or.inr (by simpa only [min_eq_right h, max_eq_left h] using And.intro h0 h1)
  obtain ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk',
      hchild, hclosure, hannulus⟩ :=
    m64Intrinsic_exists_nested_inner_return_region hU hV hpV hbV hd hcover hfront hsub
      hcircle (le_min hz.1 hw.1) (min_lt_max.mpr hzw) (max_le hz.2 hw.2)
      hperiod hT hg hi hends hprefix
  have hloss : intrinsicBoundaryLength N.metric 1 (min z w) (max z w) ≤
      intrinsicBoundaryLength N.metric 1 a b - epsilon := by
    rcases le_total z w with h | h
    · have hquant :=
        (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero hz.1 h hw.2).1
      simpa only [min_eq_left h, max_eq_right h] using
        hquant.trans (sub_le_sub_left hleft _)
    · have hquant :=
        (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero hw.1 h hz.2).2
      simpa only [min_eq_right h, max_eq_left h] using
        hquant.trans (sub_le_sub_left hright _)
  exact ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk',
    hchild, hclosure, hannulus, hloss⟩

end PoincareConjecture
