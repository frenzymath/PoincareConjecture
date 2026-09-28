import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_nested_collision_region
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {alpha beta : ℝ → AnnulusCoordinates} {a b A B : ℝ}
    (hab : a < b) (hperiod : b - a < rampPeriod) (hA : 0 < A) (hB : 0 < B)
    (ha : Continuous alpha) (hb : Continuous beta)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b)
    (haInterior : ∀ s ∈ Ioc 0 A, 1 < ‖alpha s‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U)
    (hconfA : MapsTo alpha (Icc 0 A) (closure U))
    (hconfB : MapsTo beta (Icc 0 B) (closure U)) (hmeet : alpha A = beta B) :
    ∃ s t : ℝ, 0 < s ∧ s ≤ A ∧ 0 < t ∧ t ≤ B ∧ alpha s = beta t ∧
      (∀ x ∈ Icc 0 s, ∀ y ∈ Icc 0 t, alpha x = beta y → x = s ∧ y = t) ∧
      ∃ W Y : Set AnnulusCoordinates,
        IsOpen W ∧ IsOpen Y ∧ IsPathConnected W ∧ IsPathConnected Y ∧
        Bornology.IsBounded W ∧ ¬ Bornology.IsBounded Y ∧ Disjoint W Y ∧
        W ∪ Y = (frontier W)ᶜ ∧ frontier Y = frontier W ∧
        frontier W = intrinsicAnnulusBoundary 1 '' Icc a b ∪
          (alpha '' Icc 0 s ∪ beta '' Icc 0 t) ∧
        IsCompact (closure W) ∧ W ⊆ U ∧ closure W ⊆ closure U ∧
        closure W ⊆ standardAnnulusDomain := by
  have hstart : alpha 0 ≠ beta 0 := by
    intro heq
    rw [ha0, hb0] at heq
    exact hab.ne (m64Intrinsic_boundary_injOn_short_arc hperiod
      ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ heq)
  have ha0not : alpha 0 ∉ beta '' Icc 0 B := by
    rintro ⟨t, ht, heq⟩
    by_cases ht0 : t = 0
    · exact hstart (ht0 ▸ heq.symm)
    have hnorm := hbInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
    rw [heq, ha0, m64Intrinsic_inner_boundary_norm] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  have hb0not : beta 0 ∉ alpha '' Icc 0 A := by
    rintro ⟨s, hs, heq⟩
    by_cases hs0 : s = 0
    · exact hstart (hs0 ▸ heq)
    have hnorm := haInterior s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
    rw [heq, hb0, m64Intrinsic_inner_boundary_norm] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  obtain ⟨s, t, hs, hsA, ht, htB, hst, hfirst⟩ :=
    m64Intrinsic_exists_first_crossing ha hb ha0not hb0not
      ⟨A, ⟨hA.le, le_rfl⟩, B, ⟨hB.le, le_rfl⟩, hmeet⟩
  obtain ⟨s', t', hs', hs's, ht', ht't, hst', W, Y, hW, hY, hpW, hpY,
      hbW, hbY, hWY, hcW, hfW, hfY, hkW⟩ :=
    m64Intrinsic_inward_crossing_region hab hperiod ha hb
      (hai.mono (Icc_subset_Icc_right hsA)) (hbi.mono (Icc_subset_Icc_right htB))
      ha0 hb0 (fun x hx => haInterior x ⟨hx.1, hx.2.trans hsA⟩)
      (fun y hy => hbInterior y ⟨hy.1, hy.2.trans htB⟩)
      ⟨s, ⟨hs.le, le_rfl⟩, t, ⟨ht.le, le_rfl⟩, hst⟩
  obtain ⟨rfl, rfl⟩ := hfirst s' ⟨hs'.le, hs's⟩ t' ⟨ht'.le, ht't⟩ hst'
  have hfrontSub : frontier W ⊆ closure U := by
    rw [hfW]
    refine union_subset (hcircle.trans frontier_subset_closure) (union_subset ?_ ?_)
    · rintro z ⟨x, hx, rfl⟩
      exact hconfA ⟨hx.1, hx.2.trans hsA⟩
    · rintro z ⟨y, hy, rfl⟩
      exact hconfB ⟨hy.1, hy.2.trans htB⟩
  have hchild : W ⊆ U := m64Intrinsic_jordan_nested_of_frontier_subset
    hU hV hW hY hpV hbW hbV hUV hWY hcover (by simpa only [hfW] using hcW)
      hfront hfrontSub
  exact ⟨s', t', hs', hsA, ht', htB, hst', hfirst, W, Y, hW, hY, hpW, hpY, hbW, hbY,
    hWY, by simpa only [hfW] using hcW, hfY.trans hfW.symm, hfW, hkW, hchild,
    closure_mono hchild, (closure_mono hchild).trans hsub⟩

end PoincareConjecture
