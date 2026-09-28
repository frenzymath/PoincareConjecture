import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InnerReturnRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions

noncomputable section
set_option autoImplicit false

open Set Function Metric
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_embedded_inner_return_annular_region
    {gamma : ℝ → AnnulusCoordinates} {a b T : ℝ}
    (hab : a < b) (hperiod : b - a < rampPeriod) (hT : 0 < T)
    (hg : Continuous gamma) (hi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 a)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 b)
    (hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (frontier U)ᶜ ∧ frontier V = frontier U ∧
      IsCompact (closure U) ∧ closure U ⊆ standardAnnulusDomain ∧
      (frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ gamma '' Icc 0 T ∨
        frontier U = intrinsicAnnulusBoundary 1 '' Icc b (a + rampPeriod) ∪
          gamma '' Icc 0 T) := by
  obtain ⟨U₁, V₁, hU₁, hV₁, hpU₁, hpV₁, hbU₁, hbV₁, hd₁, hc₁, hfU₁, hfV₁, hk₁⟩ :=
    m64Intrinsic_embedded_inner_return_region hab hperiod hT hg hi h0 h1
      (fun t ht => (hinside t ht).1)
  let rev : ℝ → AnnulusCoordinates := fun t => gamma (T - t)
  have hrev : Continuous rev := hg.comp (continuous_const.sub continuous_id)
  have hrevi : InjOn rev (Icc 0 T) := by
    intro s hs t ht heq
    have h := hi ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
    linarith
  have hrev0 : rev 0 = intrinsicAnnulusBoundary 1 b := by
    simpa only [rev, sub_zero] using h1
  have hrevT : rev T = intrinsicAnnulusBoundary 1 (a + rampPeriod) := by
    simpa only [rev, sub_self, m64Intrinsic_boundary_periodic 1 a] using h0
  have hrevInside : ∀ t ∈ Ioo 0 T, 1 < ‖rev t‖ := by
    intro t ht
    exact (hinside (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).1
  have hrevImage : rev '' Icc 0 T = gamma '' Icc 0 T := by
    change (gamma ∘ fun t => T - t) '' Icc 0 T = _
    rw [image_comp, image_const_sub_Icc]
    simp only [sub_self, sub_zero]
  obtain ⟨U₂, V₂, hU₂, hV₂, hpU₂, hpV₂, hbU₂, hbV₂, hd₂, hc₂, hfU₂, hfV₂, hk₂⟩ :=
    m64Intrinsic_embedded_inner_return_region (by linarith : b < a + rampPeriod)
      (by linarith : a + rampPeriod - b < rampPeriod) hT hrev hrevi hrev0 hrevT
      hrevInside
  rw [hrevImage] at hc₂ hfU₂ hfV₂
  have hgamma : gamma '' Icc 0 T ⊆ standardAnnulusDomain := by
    rintro p ⟨t, ht, rfl⟩
    by_cases ht0 : t = 0
    · subst t
      change 1 ≤ ‖gamma 0‖ ∧ ‖gamma 0‖ ≤ 2
      rw [h0, m64Intrinsic_inner_boundary_norm]
      norm_num
    by_cases htT : t = T
    · subst t
      change 1 ≤ ‖gamma T‖ ∧ ‖gamma T‖ ≤ 2
      rw [h1, m64Intrinsic_inner_boundary_norm]
      norm_num
    have h := hinside t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
      lt_of_le_of_ne ht.2 htT⟩
    exact ⟨h.1.le, h.2.le⟩
  have hcircle (J : Set ℝ) : intrinsicAnnulusBoundary 1 '' J ⊆ standardAnnulusDomain := by
    rintro p ⟨t, _, rfl⟩
    change 1 ≤ ‖intrinsicAnnulusBoundary 1 t‖ ∧ ‖intrinsicAnnulusBoundary 1 t‖ ≤ 2
    rw [m64Intrinsic_inner_boundary_norm]
    norm_num
  have htrace₁ : frontier U₁ ⊆ standardAnnulusDomain := by
    rw [hfU₁]
    exact union_subset (hcircle _) hgamma
  have htrace₂ : frontier U₂ ⊆ standardAnnulusDomain := by
    rw [hfU₂]
    exact union_subset (hcircle _) hgamma
  have hshared : frontier U₂ ⊆ frontier U₁ ∪ closedBall (0 : AnnulusCoordinates) 1 := by
    rw [hfU₂, hfU₁]
    rintro p (⟨t, _, rfl⟩ | hp)
    · exact Or.inr (by simp only [mem_closedBall, dist_zero_right,
        m64Intrinsic_inner_boundary_norm, le_refl])
    · exact Or.inl (Or.inr hp)
  let m := (a + b) / 2
  have ham : a < m := by dsimp only [m]; linarith
  have hmb : m < b := by dsimp only [m]; linarith
  let p := intrinsicAnnulusBoundary 1 m
  have hp₁ : p ∈ frontier U₁ := by rw [hfU₁]; exact Or.inl ⟨m, ⟨ham.le, hmb.le⟩, rfl⟩
  have hp₂ : p ∉ frontier U₂ := by
    rw [hfU₂]
    rintro (⟨s, hs, hsp⟩ | ⟨t, ht, htp⟩)
    · have heq := m64Intrinsic_boundary_injOn_short_arc
        (show a + rampPeriod - m < rampPeriod by linarith)
        (show s ∈ Icc m (a + rampPeriod) from ⟨hmb.le.trans hs.1, hs.2⟩)
        (show m ∈ Icc m (a + rampPeriod) from ⟨le_rfl, by linarith⟩) hsp
      linarith [hs.1]
    · by_cases ht0 : t = 0
      · subst t
        rw [h0] at htp
        have heq := m64Intrinsic_boundary_injOn_short_arc hperiod
          (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) ⟨ham.le, hmb.le⟩ htp
        exact ham.ne heq
      by_cases htT : t = T
      · subst t
        rw [h1] at htp
        have heq := m64Intrinsic_boundary_injOn_short_arc hperiod
          (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) ⟨ham.le, hmb.le⟩ htp
        exact hmb.ne heq.symm
      have h := (hinside t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 htT⟩).1
      rw [htp, m64Intrinsic_inner_boundary_norm] at h
      exact (lt_irrefl (1 : ℝ)) h
  have hc₁' : U₁ ∪ V₁ = (frontier U₁)ᶜ := by rwa [hfU₁]
  have hc₂' : U₂ ∪ V₂ = (frontier U₂)ᶜ := by rwa [hfU₂]
  rcases m64Intrinsic_one_of_two_regions_is_annular hU₁ hV₁ hU₂ hV₂
      hpV₁.isConnected.isPreconnected hbU₂ hbV₁ hd₁ hd₂ hc₁' hc₂' (hfU₁.trans hfV₁.symm)
      hk₁ hk₂ htrace₁ htrace₂ hshared (m64Intrinsic_inner_boundary_norm m) hp₁ hp₂ with h | h
  · exact ⟨U₁, V₁, hU₁, hV₁, hpU₁, hpV₁, hbU₁, hbV₁, hd₁, hc₁',
      hfV₁.trans hfU₁.symm, hk₁, h, Or.inl hfU₁⟩
  · exact ⟨U₂, V₂, hU₂, hV₂, hpU₂, hpV₂, hbU₂, hbV₂, hd₂, hc₂',
      hfV₂.trans hfU₂.symm, hk₂, h, Or.inr hfU₂⟩

end PoincareConjecture
