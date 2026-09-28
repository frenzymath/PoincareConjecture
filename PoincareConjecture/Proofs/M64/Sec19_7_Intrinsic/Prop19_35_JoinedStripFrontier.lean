import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphStripSide

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem joined_axis_contacts
    (S T : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {rho : ℝ} (hrho : 0 < rho) (hcommon : S (1, 0) = T (0, 0))
    (hsep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < rho → |w| < rho →
        (t, z) ∈ S.source ∧ (s, w) ∈ T.source ∧
          (S (t, z) = T (s, w) → t = 1 ∧ s = 0)) :
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < rho →
      S (t, z) ∈ (fun s => T (s, 0)) '' Icc (0 : ℝ) 1 → z = 0) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ w : ℝ, |w| < rho →
      T (s, w) ∈ (fun t => S (t, 0)) '' Icc (0 : ℝ) 1 → w = 0) := by
  have hz : |(0 : ℝ)| < rho := by simpa only [abs_zero] using hrho
  have hbase := hsep 1 (by simp) 0 (by simp) 0 0 hz hz
  constructor
  · rintro t ht z hzr ⟨s, hs, hst⟩
    have h := hsep t ht s hs z 0 hzr hz
    obtain ⟨rfl, rfl⟩ := h.2.2 hst.symm
    exact congrArg Prod.snd (S.injOn h.1 hbase.1 (hst.symm.trans hcommon.symm))
  · rintro s hs w hwr ⟨t, ht, hts⟩
    have h := hsep t ht s hs 0 w hz hwr
    obtain ⟨rfl, rfl⟩ := h.2.2 hts
    exact congrArg Prod.snd (T.injOn h.2.1 hbase.2.1 (hts.symm.trans hcommon))

theorem m64Intrinsic_exists_joined_strip_frontier_width
    {alpha beta : ℝ → AnnulusCoordinates} (ha : Continuous alpha) (hb : Continuous beta)
    {A0 A B B1 a b : ℝ} (ha0 : A0 ≤ a) (haA : a < A) (hBb : B < b) (hb1 : b ≤ B1)
    (hai : InjOn alpha (Icc A0 A)) (hbi : InjOn beta (Icc B B1))
    (hend : alpha A = beta B)
    (hmeet : ∀ s ∈ Icc A0 A, ∀ t ∈ Icc B B1,
      alpha s = beta t → s = A ∧ t = B)
    {K U : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoidA : ∀ t ∈ Icc a A, alpha t ∉ K)
    (havoidB : ∀ t ∈ Icc B b, beta t ∉ K)
    (hfront : frontier U = alpha '' Icc A0 A ∪ beta '' Icc B B1 ∪ K)
    (L R : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (G H : OpenPartialHomeomorph ℝ ℝ)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
    (hI : Icc a A ⊆ G.source) (hG : StrictMonoOn G G.source)
    (hgraphA : ∀ t ∈ G.source, L (alpha t) = (G t, f (G t)))
    (himageA : G '' Icc a A = Icc (G a) (G A)) (htargetA : Icc (G a) (G A) ⊆ G.target)
    (hJ : Icc B b ⊆ H.source) (hH : StrictMonoOn H H.source)
    (hgraphB : ∀ t ∈ H.source, R (beta t) = (H t, g (H t)))
    (himageB : H '' Icc B b = Icc (H B) (H b)) (htargetB : Icc (H B) (H b) ⊆ H.target)
    {ua wa ub wb uc wc ud wd : ℝ}
    (P : TransverseGraphCuts f (G a) (G A) ua wa ub wb)
    (Q : TransverseGraphCuts g (H B) (H b) uc wc ud wd)
    {rho : ℝ} (hrho : 0 < rho) :
    let S := P.linearCoordinates L.symm G.open_target hf
    let T := Q.linearCoordinates R.symm H.open_target hg
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < rho → |w| < rho →
        (t, z) ∈ S.source ∧ (s, w) ∈ T.source ∧
          (S (t, z) = T (s, w) → t = 1 ∧ s = 0)) →
    ∃ delta > 0, delta ≤ rho ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta →
        (t, z) ∈ S.source ∧ (S (t, z) ∈ frontier U ↔ z = 0)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta →
        (t, z) ∈ T.source ∧ (T (t, z) ∈ frontier U ↔ z = 0) := by
  intro S T hsep
  have haxisA := m64Intrinsic_graph_strip_axis_image L G hf hI
    (hG (hI (left_mem_Icc.mpr haA.le)) (hI (right_mem_Icc.mpr haA.le)) haA).le
    hgraphA himageA P
  have haxisB := m64Intrinsic_graph_strip_axis_image R H hg hJ
    (hH (hJ (left_mem_Icc.mpr hBb.le)) (hJ (right_mem_Icc.mpr hBb.le)) hBb).le
    hgraphB himageB Q
  have hcommon : S (1, 0) = T (0, 0) := by
    dsimp only [S, T]
    rw [P.linearCoordinates_axis, Q.linearCoordinates_axis]
    simp only [one_mul, zero_mul, add_zero, add_sub_cancel]
    rw [← hgraphA A (hI (right_mem_Icc.mpr haA.le)),
      ← hgraphB B (hJ (left_mem_Icc.mpr hBb.le)),
      L.symm_apply_apply, R.symm_apply_apply, hend]
  obtain ⟨hotherA, hotherB⟩ := joined_axis_contacts S T hrho hcommon hsep
  have hleftCell : Icc a A ⊆ Icc A0 A := Icc_subset_Icc ha0 le_rfl
  have hrightCell : Icc B b ⊆ Icc B B1 := Icc_subset_Icc le_rfl hb1
  have hsplitA : alpha '' Icc A0 A = alpha '' Icc A0 a ∪ alpha '' Icc a A := by
    rw [← image_union, Icc_union_Icc_eq_Icc ha0 haA.le]
  have hsplitB : beta '' Icc B B1 = beta '' Icc B b ∪ beta '' Icc b B1 := by
    rw [← image_union, Icc_union_Icc_eq_Icc hBb.le hb1]
  have hleftFront : frontier U = alpha '' Icc A0 A ∪
      (fun t => T (t, 0)) '' Icc (0 : ℝ) 1 ∪ (beta '' Icc b B1 ∪ K) := by
    rw [haxisB, hfront, hsplitB]
    ac_rfl
  have hrightFront : frontier U = beta '' Icc B B1 ∪
      (fun t => S (t, 0)) '' Icc (0 : ℝ) 1 ∪ (alpha '' Icc A0 a ∪ K) := by
    rw [haxisA, hfront, hsplitA]
    ac_rfl
  have hleftAvoid (s : ℝ) (hs : s ∈ Icc a A) : alpha s ∉ beta '' Icc b B1 ∪ K := by
    rintro (⟨t, ht, heq⟩ | hKpoint)
    · have he := (hmeet s (hleftCell hs) t ⟨hBb.le.trans ht.1, ht.2⟩ heq.symm).2
      exact hBb.not_ge (he ▸ ht.1)
    · exact havoidA s hs hKpoint
  have hrightAvoid (t : ℝ) (ht : t ∈ Icc B b) : beta t ∉ alpha '' Icc A0 a ∪ K := by
    rintro (⟨s, hs, heq⟩ | hKpoint)
    · have he := (hmeet s ⟨hs.1, hs.2.trans haA.le⟩ t (hrightCell ht) heq).1
      exact haA.not_ge (he ▸ hs.2)
    · exact havoidB t ht hKpoint
  obtain ⟨deltaA, hdeltaA, hdeltaArho, hstripA⟩ :=
    m64Intrinsic_exists_endpoint_strip_frontier_width ha hai haA hleftCell
      ((isCompact_Icc.image hb).union hK) hleftAvoid hleftFront
      L G hf hI hG hgraphA himageA htargetA P hrho hotherA
  obtain ⟨deltaB, hdeltaB, hdeltaBrho, hstripB⟩ :=
    m64Intrinsic_exists_endpoint_strip_frontier_width hb hbi hBb hrightCell
      ((isCompact_Icc.image ha).union hK) hrightAvoid hrightFront
      R H hg hJ hH hgraphB himageB htargetB Q hrho hotherB
  refine ⟨min deltaA deltaB, lt_min hdeltaA hdeltaB,
    (min_le_left _ _).trans hdeltaArho, ?_, ?_⟩
  · exact fun t ht z hz => hstripA t ht z (hz.trans_le (min_le_left _ _))
  · exact fun t ht z hz => hstripB t ht z (hz.trans_le (min_le_right _ _))

end PoincareConjecture
