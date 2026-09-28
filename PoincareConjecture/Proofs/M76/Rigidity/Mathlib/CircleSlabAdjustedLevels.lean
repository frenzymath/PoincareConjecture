import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleSlabPhaseSigns
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapseHomotopy











set_option autoImplicit false

open Set

namespace CollarCollapse

private theorem translated_height_control {h : ℝ → ℝ}
    {eta delta r s t : ℝ} (hr : 0 ≤ r) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (-delta) delta)
    (hbound : ∀ u ∈ Icc (-delta) delta, |h u| < eta)
    (hzero : ∀ u ∈ Icc (-delta) delta, h u = 0 ↔ u = 0)
    (hweak : ∀ u ∈ Icc (-delta) delta, 0 ≤ h u ↔ 0 ≤ u) :
    |h (move r s t) + s * displacement r t| < eta + r ∧
      (h (move r s t) + s * displacement r t = 0 ↔ t = 0) := by
  have hm := move_mem_Icc hr hs ht
  constructor
  · calc
      |h (move r s t) + s * displacement r t| ≤
          |h (move r s t)| + |s * displacement r t| := abs_add_le _ _
      _ < eta + r := add_lt_add_of_lt_of_le (hbound _ hm)
        (abs_time_displacement_le hr hs t)
  · constructor
    · intro heq
      apply (move_displacement_zero_iff hr s t).mp
      by_cases ht0 : 0 ≤ t
      · obtain ⟨hm0, _, hw0, _⟩ := move_nonneg_bounds hr hs ht0
        have hh0 : 0 ≤ h (move r s t) := (hweak _ hm).mpr hm0
        have hh : h (move r s t) = 0 := by linarith
        exact ⟨(hzero _ hm).mp hh, by linarith⟩
      · obtain ⟨hm0, _, _, hw0⟩ := move_nonpos_bounds hr hs (le_of_not_ge ht0)
        have hh0 : h (move r s t) ≤ 0 := by
          by_contra hn
          have hhpos : 0 < h (move r s t) := lt_of_not_ge hn
          have hmn : 0 ≤ move r s t := (hweak _ hm).mp hhpos.le
          have hmzero : move r s t = 0 := le_antisymm hm0 hmn
          have hhzero := (hzero _ hm).mpr hmzero
          linarith
        have hh : h (move r s t) = 0 := by linarith
        exact ⟨(hzero _ hm).mp hh, by linarith⟩
    · intro ht0
      obtain ⟨hmzero, hwzero⟩ := (move_displacement_zero_iff hr s t).mpr ht0
      rw [(hzero _ hm).mpr hmzero, hwzero, zero_add]

end CollarCollapse

namespace AddCircle

open Classical in






theorem adjusted_phase_levels_iff {E : Type*} [TopologicalSpace E]
    (p : ℝ) [Fact (0 < p)] {B : Set E} {a b eta delta r : ℝ}
    (heta : 0 < eta) (hdelta : 0 ≤ delta)
    (ha : 0 < a - 2 * eta) (hab : a + 2 * eta < b - 2 * eta)
    (hb : b + 2 * eta < p) (hr : 0 ≤ r) (hrEta : r < eta)
    {f : E × ℝ → AddCircle p} (hc : ContinuousOn f (B ×ˢ Icc (-delta) delta))
    (hf : MapsTo f (B ×ˢ Icc (-delta) delta)
      (openIntervalArc p (a - eta) (a + eta) ∪
        openIntervalArc p (b - eta) (b + eta)))
    (hside : ∀ z ∈ B ×ˢ Icc (-delta) delta,
      f z ∈ closedIntervalArc p a b ↔ 0 ≤ z.2)
    (hfront : ∀ z ∈ B ×ˢ Icc (-delta) delta,
      f z ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p)) ↔ z.2 = 0) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ B ×ˢ Icc (-delta) delta,
      (f (z.1, CollarCollapse.move r s z.2) +
          (((s * (if f (z.1, 0) = (a : AddCircle p) then 1 else -1) *
            CollarCollapse.displacement r z.2 : ℝ)) : AddCircle p) = (a : AddCircle p) ↔
        f z = (a : AddCircle p)) ∧
      (f (z.1, CollarCollapse.move r s z.2) +
          (((s * (if f (z.1, 0) = (a : AddCircle p) then 1 else -1) *
            CollarCollapse.displacement r z.2 : ℝ)) : AddCircle p) = (b : AddCircle p) ↔
        f z = (b : AddCircle p)) := by
  obtain ⟨v, _, hval, _, hlabels, hsigns⟩ :=
    exists_phase_representative_signs p heta hdelta ha hab hb hc hf hside hfront
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  have habCircle : (a : AddCircle p) ≠ (b : AddCircle p) := by
    intro heq
    have habEq := (coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq
    linarith
  rintro s hs ⟨x, t⟩ ⟨hx, ht⟩
  have hm := CollarCollapse.move_mem_Icc hr hs ht
  have hzt : (x, t) ∈ B ×ˢ Icc (-delta) delta := ⟨hx, ht⟩
  rcases hlabels x hx with hphase | hphase
  · have hlocal := (hsigns x hx).1 hphase
    have hbound (u : ℝ) (hu : u ∈ Icc (-delta) delta) : |v (x, u) - a| < eta :=
      (hlocal u hu).1
    have hzero (u : ℝ) (hu : u ∈ Icc (-delta) delta) : v (x, u) - a = 0 ↔ u = 0 :=
      sub_eq_zero.trans (hlocal u hu).2.1
    have hweak (u : ℝ) (hu : u ∈ Icc (-delta) delta) :
        0 ≤ v (x, u) - a ↔ 0 ≤ u :=
      sub_nonneg.trans (hlocal u hu).2.2.1
    obtain ⟨hsmall, hzeroMove⟩ :=
      CollarCollapse.translated_height_control hr hs ht hbound hzero hweak
    let u := v (x, CollarCollapse.move r s t) + s * CollarCollapse.displacement r t
    have hdiff : u - a = (v (x, CollarCollapse.move r s t) - a) +
        s * CollarCollapse.displacement r t := by dsimp only [u]; ring
    have huBound : |u - a| < 2 * eta := by
      rw [hdiff]
      exact hsmall.trans (by linarith)
    have huZero : u = a ↔ t = 0 := by
      calc
        u = a ↔ u - a = 0 := sub_eq_zero.symm
        _ ↔ (v (x, CollarCollapse.move r s t) - a) +
            s * CollarCollapse.displacement r t = 0 := by rw [hdiff]
        _ ↔ t = 0 := hzeroMove
    have huI : u ∈ Ico (0 : ℝ) (0 + p) := by
      obtain ⟨hl, hu⟩ := abs_lt.mp huBound
      constructor <;> linarith
    have hub : u < b := by have := (abs_lt.mp huBound).2; linarith
    have hcastA : (u : AddCircle p) = (a : AddCircle p) ↔ t = 0 :=
      (coe_eq_coe_iff_of_mem_Ico huI haI).trans huZero
    have hcastB : (u : AddCircle p) ≠ (b : AddCircle p) :=
      fun heq => (ne_of_lt hub) ((coe_eq_coe_iff_of_mem_Ico huI hbI).mp heq)
    have horigA : f (x, t) = (a : AddCircle p) ↔ t = 0 := by
      constructor
      · intro heq
        exact (hfront (x, t) hzt).mp (Or.inl heq)
      · intro ht0
        simpa only [ht0] using hphase
    have horigB : f (x, t) ≠ (b : AddCircle p) := by
      intro heq
      have ht0 : t = 0 := (hfront (x, t) hzt).mp (Or.inr heq)
      have hzeroB : f (x, 0) = (b : AddCircle p) :=
        (congrArg (fun u : ℝ => f (x, u)) ht0).symm.trans heq
      exact habCircle (hphase.symm.trans hzeroB)
    have hformula : f (x, CollarCollapse.move r s t) +
        (((s * (if f (x, 0) = (a : AddCircle p) then 1 else -1) *
          CollarCollapse.displacement r t : ℝ)) : AddCircle p) = (u : AddCircle p) := by
      rw [← hval (x, CollarCollapse.move r s t) ⟨hx, hm⟩, if_pos hphase]
      simp only [mul_one, ← coe_add, u]
    rw [hformula]
    exact ⟨hcastA.trans horigA.symm, iff_of_false hcastB horigB⟩
  · change f (x, 0) = (b : AddCircle p) at hphase
    have hlocal := (hsigns x hx).2 hphase
    have hbound (u : ℝ) (hu : u ∈ Icc (-delta) delta) : |b - v (x, u)| < eta := by
      rw [abs_sub_comm]
      exact (hlocal u hu).1
    have hzero (u : ℝ) (hu : u ∈ Icc (-delta) delta) : b - v (x, u) = 0 ↔ u = 0 := by
      rw [sub_eq_zero, eq_comm]
      exact (hlocal u hu).2.1
    have hweak (u : ℝ) (hu : u ∈ Icc (-delta) delta) :
        0 ≤ b - v (x, u) ↔ 0 ≤ u :=
      sub_nonneg.trans (hlocal u hu).2.2.1
    obtain ⟨hsmall, hzeroMove⟩ :=
      CollarCollapse.translated_height_control hr hs ht hbound hzero hweak
    let u := v (x, CollarCollapse.move r s t) - s * CollarCollapse.displacement r t
    have hdiff : b - u = (b - v (x, CollarCollapse.move r s t)) +
        s * CollarCollapse.displacement r t := by dsimp only [u]; ring
    have huBound : |u - b| < 2 * eta := by
      rw [abs_sub_comm, hdiff]
      exact hsmall.trans (by linarith)
    have huZero : u = b ↔ t = 0 := by
      calc
        u = b ↔ b - u = 0 := by rw [sub_eq_zero, eq_comm]
        _ ↔ (b - v (x, CollarCollapse.move r s t)) +
            s * CollarCollapse.displacement r t = 0 := by rw [hdiff]
        _ ↔ t = 0 := hzeroMove
    have huI : u ∈ Ico (0 : ℝ) (0 + p) := by
      obtain ⟨hl, hu⟩ := abs_lt.mp huBound
      constructor <;> linarith
    have hau : a < u := by have := (abs_lt.mp huBound).1; linarith
    have hcastB : (u : AddCircle p) = (b : AddCircle p) ↔ t = 0 :=
      (coe_eq_coe_iff_of_mem_Ico huI hbI).trans huZero
    have hcastA : (u : AddCircle p) ≠ (a : AddCircle p) :=
      fun heq => (ne_of_gt hau) ((coe_eq_coe_iff_of_mem_Ico huI haI).mp heq)
    have horigB : f (x, t) = (b : AddCircle p) ↔ t = 0 := by
      constructor
      · intro heq
        exact (hfront (x, t) hzt).mp (Or.inr heq)
      · intro ht0
        simpa only [ht0] using hphase
    have hnotA : f (x, 0) ≠ (a : AddCircle p) :=
      fun heq => habCircle (heq.symm.trans hphase)
    have horigA : f (x, t) ≠ (a : AddCircle p) := by
      intro heq
      have ht0 : t = 0 := (hfront (x, t) hzt).mp (Or.inl heq)
      exact hnotA ((congrArg (fun u : ℝ => f (x, u)) ht0).symm.trans heq)
    have hformula : f (x, CollarCollapse.move r s t) +
        (((s * (if f (x, 0) = (a : AddCircle p) then 1 else -1) *
          CollarCollapse.displacement r t : ℝ)) : AddCircle p) = (u : AddCircle p) := by
      rw [← hval (x, CollarCollapse.move r s t) ⟨hx, hm⟩, if_neg hnotA]
      have hmul : s * (-1) * CollarCollapse.displacement r t =
          -(s * CollarCollapse.displacement r t) := by ring
      simp only [hmul, ← coe_add, u, sub_eq_add_neg]
    rw [hformula]
    exact ⟨iff_of_false hcastA horigA, hcastB.trans horigB.symm⟩

end AddCircle
