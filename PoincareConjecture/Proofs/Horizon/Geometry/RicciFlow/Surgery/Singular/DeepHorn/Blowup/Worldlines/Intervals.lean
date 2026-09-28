import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace PoincareConjecture.DeepHorn

theorem overlapping_intervals_local {I J : Set ℝ}
    (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {a : ℝ} (haI : a ∈ interior I) (haJ : a ∈ interior J)
    {s : ℝ} (hs : s ∈ I ∪ J) :
    ∃ K : Set ℝ, (K = I ∨ K = J) ∧ s ∈ K ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ t ∈ I ∪ J, |t - s| < delta → t ∈ K := by
  have hside {I J : Set ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
      (haI : a ∈ I) (haJ : a ∈ J) (hsI : s ∈ I) (hsJ : s ∉ J) :
      ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ I ∪ J, |t - s| < delta → t ∈ I := by
    have hsa : s ≠ a := fun h => hsJ (h.symm ▸ haJ)
    refine ⟨|s - a|, abs_pos.mpr (sub_ne_zero.mpr hsa), ?_⟩
    intro t ht hclose
    rcases ht with ht | ht
    · exact ht
    rcases lt_or_gt_of_ne hsa with hsa | has
    · have hst : s ≤ t := by
        by_contra h
        exact hsJ (hJ.out ht haJ ⟨(lt_of_not_ge h).le, hsa.le⟩)
      apply hI.out hsI haI
      rw [abs_of_neg (sub_neg.mpr hsa)] at hclose
      exact ⟨hst, by linarith [le_abs_self (t - s)]⟩
    · have hts : t ≤ s := by
        by_contra h
        exact hsJ (hJ.out haJ ht ⟨has.le, (lt_of_not_ge h).le⟩)
      apply hI.out haI hsI
      rw [abs_of_pos (sub_pos.mpr has)] at hclose
      exact ⟨by linarith [neg_le_abs (t - s)], hts⟩
  by_cases hsI : s ∈ I
  · by_cases hsJ : s ∈ J
    · rcases lt_trichotomy s a with hsa | rfl | has
      · by_cases hleft : ∃ c ∈ I ∪ J, c < s
        · obtain ⟨c, hc, hcs⟩ := hleft
          rcases hc with hc | hc
          · refine ⟨I, Or.inl rfl, hsI, min (s - c) (a - s),
              lt_min (sub_pos.mpr hcs) (sub_pos.mpr hsa), ?_⟩
            intro t _ ht
            exact hI.out hc (interior_subset haI)
              ⟨by linarith [(lt_min_iff.mp ht).1, neg_le_abs (t - s)],
                by linarith [(lt_min_iff.mp ht).2, le_abs_self (t - s)]⟩
          · refine ⟨J, Or.inr rfl, hsJ, min (s - c) (a - s),
              lt_min (sub_pos.mpr hcs) (sub_pos.mpr hsa), ?_⟩
            intro t _ ht
            exact hJ.out hc (interior_subset haJ)
              ⟨by linarith [(lt_min_iff.mp ht).1, neg_le_abs (t - s)],
                by linarith [(lt_min_iff.mp ht).2, le_abs_self (t - s)]⟩
        · refine ⟨I, Or.inl rfl, hsI, a - s, sub_pos.mpr hsa, ?_⟩
          intro t ht hclose
          exact hI.out hsI (interior_subset haI) ⟨le_of_not_gt (fun h => hleft ⟨t, ht, h⟩),
            by linarith [le_abs_self (t - s)]⟩
      · obtain ⟨delta, hd, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp haI)
        refine ⟨I, Or.inl rfl, hsI, delta, hd, ?_⟩
        intro t _ ht
        exact hball (by simpa only [Metric.mem_ball, Real.dist_eq] using ht)
      · by_cases hright : ∃ b ∈ I ∪ J, s < b
        · obtain ⟨b, hb, hsb⟩ := hright
          rcases hb with hb | hb
          · refine ⟨I, Or.inl rfl, hsI, min (s - a) (b - s),
              lt_min (sub_pos.mpr has) (sub_pos.mpr hsb), ?_⟩
            intro t _ ht
            exact hI.out (interior_subset haI) hb
              ⟨by linarith [(lt_min_iff.mp ht).1, neg_le_abs (t - s)],
                by linarith [(lt_min_iff.mp ht).2, le_abs_self (t - s)]⟩
          · refine ⟨J, Or.inr rfl, hsJ, min (s - a) (b - s),
              lt_min (sub_pos.mpr has) (sub_pos.mpr hsb), ?_⟩
            intro t _ ht
            exact hJ.out (interior_subset haJ) hb
              ⟨by linarith [(lt_min_iff.mp ht).1, neg_le_abs (t - s)],
                by linarith [(lt_min_iff.mp ht).2, le_abs_self (t - s)]⟩
        · refine ⟨I, Or.inl rfl, hsI, s - a, sub_pos.mpr has, ?_⟩
          intro t ht hclose
          exact hI.out (interior_subset haI) hsI
            ⟨by linarith [neg_le_abs (t - s)], le_of_not_gt (fun h => hright ⟨t, ht, h⟩)⟩
    · exact ⟨I, Or.inl rfl, hsI, hside hI hJ (interior_subset haI) (interior_subset haJ) hsI hsJ⟩
  · have hsJ := hs.resolve_left hsI
    obtain ⟨delta, hd, hlocal⟩ :=
      hside hJ hI (interior_subset haJ) (interior_subset haI) hsJ hsI
    exact ⟨J, Or.inr rfl, hsJ, delta, hd, fun t ht => hlocal t (ht.symm)⟩

theorem interval_contains_of_uniform_backward_extension
    {I : Set ℝ} (hI : I.OrdConnected) (hzero : 0 ∈ I)
    (hnegative : ∃ s ∈ I, s < 0) {T c : ℝ} (hc : 0 < c)
    (hext : ∀ s ∈ interior I, -T < s → s < 0 → Ioc (s - c) s ⊆ I) :
    Icc (-T) 0 ⊆ I := by
  intro z hz
  by_contra hzI
  have hlow : ∀ y ∈ I, z < y := by
    intro y hy
    by_contra hzy
    exact hzI (hI.out hy hzero ⟨le_of_not_gt hzy, hz.2⟩)
  have hbdd : BddBelow I := ⟨z, fun y hy => (hlow y hy).le⟩
  have hne : I.Nonempty := ⟨0, hzero⟩
  let a := sInf I
  have haz : z ≤ a := le_csInf hne (fun y hy => (hlow y hy).le)
  obtain ⟨v, hv, hv0⟩ := hnegative
  have ha0 : a < 0 := (csInf_le hbdd hv).trans_lt hv0
  let b := min (a + c / 2) 0
  have hab : a < b := lt_min (by linarith) ha0
  obtain ⟨y, hy, hyb⟩ := exists_lt_of_csInf_lt hne hab
  have hay : a ≤ y := csInf_le hbdd hy
  have hb0 : b ≤ 0 := min_le_right _ _
  have hbc : b ≤ a + c / 2 := min_le_left _ _
  let s := (y + b) / 2
  have hys : y < s := by dsimp [s]; linarith
  have hsb : s < b := by dsimp [s]; linarith
  have hs0 : s < 0 := hsb.trans_le hb0
  have hs : s ∈ interior I := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hys, hs0⟩)
      (fun t ht => hI.out hy hzero ⟨ht.1.le, ht.2.le⟩)
  have hsT : -T < s := by linarith [hz.1]
  have hxI : s - 3 * c / 4 ∈ I := hext s hs hsT hs0 ⟨by linarith, by linarith⟩
  have hax : a ≤ s - 3 * c / 4 := csInf_le hbdd hxI
  linarith

end PoincareConjecture.DeepHorn
