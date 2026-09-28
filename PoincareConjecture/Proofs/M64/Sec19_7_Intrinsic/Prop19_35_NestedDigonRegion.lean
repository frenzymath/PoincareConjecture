import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_nested_digon_region
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V)
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (ha : ContinuousOn alpha (Icc 0 A)) (hb : ContinuousOn beta (Icc 0 B))
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hconfA : MapsTo alpha (Icc 0 A) (closure U))
    (hconfB : MapsTo beta (Icc 0 B) (closure U)) :
    ∃ W Y : Set AnnulusCoordinates,
      IsOpen W ∧ IsOpen Y ∧ IsPathConnected W ∧ IsPathConnected Y ∧
      Bornology.IsBounded W ∧ ¬ Bornology.IsBounded Y ∧ Disjoint W Y ∧
      W ∪ Y = (frontier W)ᶜ ∧
      frontier W = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∧
      frontier Y = frontier W ∧ IsCompact (closure W) ∧
      W ⊆ U ∧ closure W ⊆ closure U ∧ closure W ∪ closure Y = univ := by
  obtain ⟨loop, hl, he, hi, himage⟩ := m64Intrinsic_exists_simple_loop_between_arcs
    hA hB ha hb hai hbi hbase.symm hend.symm hmeet
  obtain ⟨W, Y, hW, hY, hpW, hpY, hbW, hbY, hWY, hcW, hfW, hfY, hkW⟩ :=
    m64Intrinsic_exists_jordan_region (by norm_num : (0 : ℝ) < 2) hl he hi
  have hfrontSub : frontier W ⊆ closure U := by
    rw [hfW, himage]
    exact union_subset (mapsTo_iff_image_subset.mp hconfA) (mapsTo_iff_image_subset.mp hconfB)
  have hchild : W ⊆ U := m64Intrinsic_jordan_nested_of_frontier_subset
    hU hV hW hY hpV hbW hbV hUV hWY hcover (by simpa only [hfW] using hcW)
      hfront hfrontSub
  have hclosedCover : closure W ∪ closure Y = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ frontier W
    · exact Or.inl (frontier_subset_closure hp)
    · have hp' : p ∈ W ∪ Y := by
        simpa only [hcW, ← hfW, mem_compl_iff] using hp
      exact hp'.elim (fun h => Or.inl (subset_closure h))
        (fun h => Or.inr (subset_closure h))
  exact ⟨W, Y, hW, hY, hpW, hpY, hbW, hbY, hWY,
    by simpa only [hfW] using hcW,
    hfW.trans himage, hfY.trans hfW.symm, hkW, hchild, closure_mono hchild, hclosedCover⟩

end PoincareConjecture
