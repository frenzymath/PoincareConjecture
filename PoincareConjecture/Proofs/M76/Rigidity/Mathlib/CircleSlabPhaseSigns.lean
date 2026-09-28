import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CirclePhaseFibers

set_option autoImplicit false

open Set

namespace AddCircle

private theorem strict_signs_of_nonneg_zero {h t : ℝ}
    (hzero : h = 0 ↔ t = 0) (hnonneg : 0 ≤ h ↔ 0 ≤ t) :
    (0 < h ↔ 0 < t) ∧ (h < 0 ↔ t < 0) := by
  constructor
  · constructor
    · intro hh
      have htn : t ≠ 0 := fun ht => (ne_of_gt hh) (hzero.mpr ht)
      exact lt_of_le_of_ne (hnonneg.mp hh.le) (Ne.symm htn)
    · intro ht
      have hhn : h ≠ 0 := fun hh => (ne_of_gt ht) (hzero.mp hh)
      exact lt_of_le_of_ne (hnonneg.mpr ht.le) (Ne.symm hhn)
  · simpa only [not_le] using not_congr hnonneg

theorem exists_phase_representative_signs {E : Type*} [TopologicalSpace E]
    (p : ℝ) [Fact (0 < p)] {B : Set E} {a b eta delta : ℝ}
    (heta : 0 < eta) (hdelta : 0 ≤ delta)
    (ha : 0 < a - 2 * eta) (hab : a + 2 * eta < b - 2 * eta)
    (hb : b + 2 * eta < p)
    {f : E × ℝ → AddCircle p} (hc : ContinuousOn f (B ×ˢ Icc (-delta) delta))
    (hf : MapsTo f (B ×ˢ Icc (-delta) delta)
      (openIntervalArc p (a - eta) (a + eta) ∪
        openIntervalArc p (b - eta) (b + eta)))
    (hside : ∀ z ∈ B ×ˢ Icc (-delta) delta,
      f z ∈ closedIntervalArc p a b ↔ 0 ≤ z.2)
    (hfront : ∀ z ∈ B ×ˢ Icc (-delta) delta,
      f z ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p)) ↔ z.2 = 0) :
    ∃ v : E × ℝ → ℝ, ContinuousOn v (B ×ˢ Icc (-delta) delta) ∧
      (∀ z ∈ B ×ˢ Icc (-delta) delta, (v z : AddCircle p) = f z) ∧
      (∀ z ∈ B ×ˢ Icc (-delta) delta, v z ∈ Ioo (0 : ℝ) p) ∧
      (∀ x ∈ B, f (x, 0) ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p))) ∧
      ∀ x ∈ B,
        (f (x, 0) = (a : AddCircle p) → ∀ t ∈ Icc (-delta) delta,
          |v (x, t) - a| < eta ∧ (v (x, t) = a ↔ t = 0) ∧
          (a ≤ v (x, t) ↔ 0 ≤ t) ∧ (a < v (x, t) ↔ 0 < t) ∧
          (v (x, t) < a ↔ t < 0)) ∧
        (f (x, 0) = (b : AddCircle p) → ∀ t ∈ Icc (-delta) delta,
          |v (x, t) - b| < eta ∧ (v (x, t) = b ↔ t = 0) ∧
          (v (x, t) ≤ b ↔ 0 ≤ t) ∧ (v (x, t) < b ↔ 0 < t) ∧
          (b < v (x, t) ↔ t < 0)) := by
  have ha0 : 0 < a := by linarith
  have hbtop : b < p := by linarith
  have haa : 0 ≤ a - eta := by linarith
  have habb : a + eta ≤ b - eta := by linarith
  have hbb : b + eta ≤ p := by linarith
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  obtain ⟨v, hvc, hval, hperiod, hvlower, hvupper⟩ :=
    exists_real_lift_on_phase_arcs p heta.le haa habb hbb hc hf
  have hfiber := mapsTo_phase_arc_on_fibers p heta hdelta haa habb hbb hc hf
  have hzero (x : E) (hx : x ∈ B) :
      f (x, 0) ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p)) :=
    (hfront (x, 0) ⟨hx, neg_nonpos.mpr hdelta, hdelta⟩).mpr rfl
  refine ⟨v, hvc, hval, hperiod, hzero, ?_⟩
  intro x hx
  constructor
  · intro hphase t ht
    have hz : (x, t) ∈ B ×ˢ Icc (-delta) delta := ⟨hx, ht⟩
    have hbounds : v (x, t) ∈ Ioo (a - eta) (a + eta) :=
      (hvlower (x, t) hz).mp ((hfiber x hx).1 hphase ht)
    have hvI : v (x, t) ∈ Ico (0 : ℝ) (0 + p) := by
      simpa only [zero_add] using
        (show v (x, t) ∈ Ico (0 : ℝ) p from
          ⟨(hperiod (x, t) hz).1.le, (hperiod (x, t) hz).2⟩)
    have heq : v (x, t) = a ↔ t = 0 := by
      constructor
      · intro hv
        apply (hfront (x, t) hz).mp
        rw [← hval (x, t) hz, hv]
        exact Or.inl rfl
      · intro ht0
        apply (coe_eq_coe_iff_of_mem_Ico hvI haI).mp
        exact (hval (x, t) hz).trans (by simpa only [ht0] using hphase)
    have hweak : a ≤ v (x, t) ↔ 0 ≤ t := by
      have hslab : v (x, t) ∈ Icc a b ↔ 0 ≤ t := by
        have h := hside (x, t) hz
        rw [← hval (x, t) hz,
          coe_mem_closedIntervalArc_iff p ha0.le hbtop
            ⟨(hperiod (x, t) hz).1.le, (hperiod (x, t) hz).2⟩] at h
        exact h
      constructor
      · intro hv
        exact hslab.mp ⟨hv, by linarith [hbounds.2]⟩
      · intro ht0
        exact (hslab.mpr ht0).1
    have hsigns : (a < v (x, t) ↔ 0 < t) ∧ (v (x, t) < a ↔ t < 0) := by
      simpa only [sub_pos, sub_neg] using
        strict_signs_of_nonneg_zero (sub_eq_zero.trans heq) (sub_nonneg.trans hweak)
    exact ⟨abs_lt.mpr ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩,
      heq, hweak, hsigns.1, hsigns.2⟩
  · intro hphase t ht
    have hz : (x, t) ∈ B ×ˢ Icc (-delta) delta := ⟨hx, ht⟩
    have hbounds : v (x, t) ∈ Ioo (b - eta) (b + eta) :=
      (hvupper (x, t) hz).mp ((hfiber x hx).2 hphase ht)
    have hvI : v (x, t) ∈ Ico (0 : ℝ) (0 + p) := by
      simpa only [zero_add] using
        (show v (x, t) ∈ Ico (0 : ℝ) p from
          ⟨(hperiod (x, t) hz).1.le, (hperiod (x, t) hz).2⟩)
    have heq : v (x, t) = b ↔ t = 0 := by
      constructor
      · intro hv
        apply (hfront (x, t) hz).mp
        rw [← hval (x, t) hz, hv]
        exact Or.inr rfl
      · intro ht0
        apply (coe_eq_coe_iff_of_mem_Ico hvI hbI).mp
        exact (hval (x, t) hz).trans (by simpa only [ht0] using hphase)
    have hweak : v (x, t) ≤ b ↔ 0 ≤ t := by
      have hslab : v (x, t) ∈ Icc a b ↔ 0 ≤ t := by
        have h := hside (x, t) hz
        rw [← hval (x, t) hz,
          coe_mem_closedIntervalArc_iff p ha0.le hbtop
            ⟨(hperiod (x, t) hz).1.le, (hperiod (x, t) hz).2⟩] at h
        exact h
      constructor
      · intro hv
        exact hslab.mp ⟨by linarith [hbounds.1], hv⟩
      · intro ht0
        exact (hslab.mpr ht0).2
    have hzero' : b - v (x, t) = 0 ↔ t = 0 := by
      rw [sub_eq_zero, eq_comm]
      exact heq
    have hsigns : (v (x, t) < b ↔ 0 < t) ∧ (b < v (x, t) ↔ t < 0) := by
      simpa only [sub_pos, sub_neg] using
        strict_signs_of_nonneg_zero hzero' (sub_nonneg.trans hweak)
    exact ⟨abs_lt.mpr ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩,
      heq, hweak, hsigns.1, hsigns.2⟩

end AddCircle
