import PoincareConjecture.Statements.M67

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m67_finite_event_gap (E : Finset ℝ) (s : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t ∈ E, t ≠ s → delta ≤ |t - s| := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a E ha ih =>
    obtain ⟨delta, hd, hgap⟩ := ih
    by_cases has : a = s
    · refine ⟨delta, hd, ?_⟩
      intro t ht hts
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact False.elim (hts has)
      · exact hgap t ht hts
    · refine ⟨min delta |a - s|, lt_min hd (abs_pos.mpr (sub_ne_zero.mpr has)), ?_⟩
      intro t ht hts
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hgap t ht hts)

theorem m67_exists_right_regular_interval
    {F : SurgeryFlowData.{u}} {T : ℝ}
    {W : RepairedEventChildWitness F}
    (P : RepairedComponentPath F T W)
    (s : Set.Icc (0 : ℝ) T) (hs : s.1 < T) :
    ∃ b : ℝ, s.1 < b ∧ b ≤ T ∧ Disjoint F.surgery_times (Set.Ioc s.1 b) := by
  obtain ⟨delta, hd, hgap⟩ := m67_finite_event_gap P.surgery_times s.1
  let b := min T (s.1 + delta / 2)
  have hsb : s.1 < b := lt_min hs (by linarith)
  refine ⟨b, hsb, min_le_left _ _, Set.disjoint_left.mpr ?_⟩
  intro t ht hinterval
  have htP : t ∈ P.surgery_times := by
    change t ∈ (↑P.surgery_times : Set ℝ)
    rw [P.surgery_times_eq]
    exact ⟨ht, s.2.1.trans hinterval.1.le,
      hinterval.2.trans (min_le_left _ _)⟩
  have h := hgap t htP (ne_of_gt hinterval.1)
  rw [abs_of_pos (sub_pos.mpr hinterval.1)] at h
  have ht' := hinterval.2.trans (min_le_right T (s.1 + delta / 2))
  linarith

theorem m67_exists_regular_neighborhood
    {F : SurgeryFlowData.{u}} {T : ℝ}
    {W : RepairedEventChildWitness F}
    (P : RepairedComponentPath F T W) (hT : 0 < T)
    (s : Set.Icc (0 : ℝ) T)
    (hs : s.1 ∉ (↑P.surgery_times : Set ℝ)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ T ∧ s.1 ∈ Set.Icc a b ∧
      Disjoint F.surgery_times (Set.Ioc a b) ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ t : Set.Icc (0 : ℝ) T, |t.1 - s.1| < delta → t.1 ∈ Set.Icc a b := by
  obtain ⟨delta, hd, hgap⟩ := m67_finite_event_gap P.surgery_times s.1
  let a := max 0 (s.1 - delta / 2)
  let b := min T (s.1 + delta / 2)
  have ha : 0 ≤ a := le_max_left _ _
  have hb : b ≤ T := min_le_left _ _
  have hab : a < b := by
    dsimp [a, b]
    rw [max_lt_iff]
    exact ⟨lt_min hT (by linarith [s.2.1]),
      lt_min (by linarith [s.2.2]) (by linarith)⟩
  have hsa : a ≤ s.1 := max_le s.2.1 (by linarith)
  have hsb : s.1 ≤ b := le_min s.2.2 (by linarith)
  refine ⟨a, b, ha, hab, hb, ⟨hsa, hsb⟩, ?_, delta / 2, by linarith, ?_⟩
  · apply Set.disjoint_left.mpr
    intro t ht hinterval
    have htP : t ∈ P.surgery_times := by
      change t ∈ (↑P.surgery_times : Set ℝ)
      rw [P.surgery_times_eq]
      exact ⟨ht, ha.trans hinterval.1.le, hinterval.2.trans hb⟩
    have hts : t ≠ s.1 := by
      intro heq
      apply hs
      simpa [heq] using htP
    have h := hgap t htP hts
    have hlow := (le_max_right 0 (s.1 - delta / 2)).trans_lt hinterval.1
    have hupp := hinterval.2.trans (min_le_right T (s.1 + delta / 2))
    have : |t - s.1| < delta := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  · intro t ht
    obtain ⟨hlow, hupp⟩ := abs_lt.mp ht
    exact ⟨max_le t.2.1 (by linarith), le_min t.2.2 (by linarith)⟩

end PoincareConjecture
