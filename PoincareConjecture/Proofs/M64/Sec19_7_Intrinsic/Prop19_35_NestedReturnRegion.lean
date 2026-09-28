import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InnerReturnRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalContactComparison












noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_exists_nested_inner_return_region
    {U V : Set AnnulusCoordinates}
    (hU : IsOpen U) (hV : IsOpen V) (hpV : IsPreconnected V)
    (hbV : ¬ Bornology.IsBounded V) (hd : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b c d T : ℝ}
    (hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hperiod : b - a < rampPeriod) (hT : 0 < T)
    {gamma : ℝ → AnnulusCoordinates}
    (hg : Continuous gamma) (hi : InjOn gamma (Icc 0 T))
    (hends : (gamma 0 = intrinsicAnnulusBoundary 1 c ∧
        gamma T = intrinsicAnnulusBoundary 1 d) ∨
      (gamma 0 = intrinsicAnnulusBoundary 1 d ∧
        gamma T = intrinsicAnnulusBoundary 1 c))
    (hprefix : ∀ t ∈ Ioo 0 T, gamma t ∈ U) :
    ∃ U' V' : Set AnnulusCoordinates,
      IsOpen U' ∧ IsOpen V' ∧ IsPathConnected U' ∧ IsPathConnected V' ∧
      Bornology.IsBounded U' ∧ ¬ Bornology.IsBounded V' ∧ Disjoint U' V' ∧
      U' ∪ V' = (intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 T)ᶜ ∧
      frontier U' = intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 T ∧
      frontier V' = intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 T ∧
      IsCompact (closure U') ∧ U' ⊆ U ∧ closure U' ⊆ closure U ∧
      closure U' ⊆ standardAnnulusDomain := by
  have hshort : d - c < rampPeriod := by linarith
  have hnorm : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖ := by
    intro t ht
    exact (m64Intrinsic_open_region_strictly_inside_annulus hU hsub
      (gamma t) (hprefix t ht)).1
  have hregion : ∃ U' V' : Set AnnulusCoordinates,
      IsOpen U' ∧ IsOpen V' ∧ IsPathConnected U' ∧ IsPathConnected V' ∧
      Bornology.IsBounded U' ∧ ¬ Bornology.IsBounded V' ∧ Disjoint U' V' ∧
      U' ∪ V' = (intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 T)ᶜ ∧
      frontier U' = intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 T ∧
      frontier V' = intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 T ∧
      IsCompact (closure U') := by
    rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact m64Intrinsic_embedded_inner_return_region hcd hshort hT hg hi h0 h1 hnorm
    · let rev : ℝ → AnnulusCoordinates := fun t => gamma (T - t)
      have hrev : Continuous rev :=
        hg.comp (continuous_const.sub continuous_id)
      have hrevi : InjOn rev (Icc 0 T) := by
        intro s hs t ht heq
        have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
          ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
        linarith
      have hrev0 : rev 0 = intrinsicAnnulusBoundary 1 c := by
        simpa only [rev, sub_zero] using h1
      have hrevT : rev T = intrinsicAnnulusBoundary 1 d := by
        simpa only [rev, sub_self] using h0
      have hrevInside : ∀ t ∈ Ioo 0 T, 1 < ‖rev t‖ := by
        intro t ht
        exact hnorm (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hrevImage : rev '' Icc 0 T = gamma '' Icc 0 T := by
        change (gamma ∘ fun t => T - t) '' Icc 0 T = _
        rw [image_comp, image_const_sub_Icc]
        simp only [sub_self, sub_zero]
      obtain ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk'⟩ :=
        m64Intrinsic_embedded_inner_return_region hcd hshort hT
          hrev hrevi hrev0 hrevT hrevInside
      rw [hrevImage] at hc' hfU' hfV'
      exact ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk'⟩
  obtain ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk'⟩ := hregion
  have hcircleSub : intrinsicAnnulusBoundary 1 '' Icc c d ⊆ frontier U :=
    (image_mono (Icc_subset_Icc hac hdb)).trans hcircle
  have hgammaClosure : gamma '' Icc 0 T ⊆ closure U := by
    rw [← closure_Ioo hT.ne]
    apply (image_closure_subset_closure_image hg).trans
    apply closure_mono
    rintro _ ⟨t, ht, rfl⟩
    exact hprefix t ht
  have hfrontSub : frontier U' ⊆ closure U := by
    rw [hfU']
    exact union_subset (hcircleSub.trans frontier_subset_closure) hgammaClosure
  have hchild : U' ⊆ U :=
    m64Intrinsic_jordan_nested_of_frontier_subset hU hV hU' hV'
      hpV hbU' hbV hd hd' hcover (by simpa only [hfU'] using hc') hfront hfrontSub
  have hclosure : closure U' ⊆ closure U := closure_mono hchild
  exact ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk',
    hchild, hclosure, hclosure.trans hsub⟩

end PoincareConjecture
