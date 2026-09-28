import PoincareConjecture.Proofs.M76.Mathlib.PLAnnularStrip

set_option autoImplicit false

open Set

namespace PLAnnularStrip

def rightStrip (L d : ℝ) : Set (ℝ × ℝ) :=
  {p | L - p.1 ∈ Icc (-d) d ∧ p.2 ∈ Icc (L - p.1) p.1}

def topStrip (L d : ℝ) : Set (ℝ × ℝ) :=
  {p | L - p.2 ∈ Icc (-d) d ∧ p.1 ∈ Icc (L - p.2) p.2}

def leftStrip (L d : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-d) d ∧ p.2 ∈ Icc p.1 (L - p.1)}

def squareAnnulus (L d : ℝ) : Set (ℝ × ℝ) :=
  (Icc (-d) (L + d) ×ˢ Icc (-d) (L + d)) \ (Ioo d (L - d) ×ˢ Ioo d (L - d))

theorem trapezoid_inter_rightStrip {L d : ℝ} (hwidth : 2 * d < L) :
    trapezoid L d ∩ rightStrip L d =
      (fun t : ℝ => (L - t, t)) '' Icc (-d) d := by
  ext p
  constructor
  · rintro ⟨⟨ht, hx⟩, ⟨_, hy⟩⟩
    refine ⟨p.2, ht, Prod.ext ?_ rfl⟩
    linarith [hx.2, hy.1]
  · rintro ⟨t, ht, rfl⟩
    change (t ∈ Icc (-d) d ∧ L - t ∈ Icc t (L - t)) ∧
      (L - (L - t) ∈ Icc (-d) d ∧ t ∈ Icc (L - (L - t)) (L - t))
    constructor
    · exact ⟨ht, by constructor <;> linarith [ht.2]⟩
    · constructor
      · simpa only [sub_sub_cancel] using ht
      · constructor <;> linarith [ht.2]

theorem topStrip_inter_rightStrip {L d : ℝ} (hwidth : 2 * d < L) :
    topStrip L d ∩ rightStrip L d =
      (fun t : ℝ => (L - t, L - t)) '' Icc (-d) d := by
  ext p
  constructor
  · rintro ⟨⟨ht, hx⟩, ⟨_, hy⟩⟩
    refine ⟨L - p.2, ht, Prod.ext ?_ ?_⟩ <;> linarith [hx.2, hy.2]
  · rintro ⟨t, ht, rfl⟩
    change (L - (L - t) ∈ Icc (-d) d ∧ L - t ∈ Icc (L - (L - t)) (L - t)) ∧
      (L - (L - t) ∈ Icc (-d) d ∧ L - t ∈ Icc (L - (L - t)) (L - t))
    have h : L - (L - t) ∈ Icc (-d) d ∧
        L - t ∈ Icc (L - (L - t)) (L - t) := by
      constructor
      · simpa only [sub_sub_cancel] using ht
      · constructor <;> linarith [ht.2]
    exact ⟨h, h⟩

theorem topStrip_inter_leftStrip {L d : ℝ} (hwidth : 2 * d < L) :
    topStrip L d ∩ leftStrip L d =
      (fun t : ℝ => (t, L - t)) '' Icc (-d) d := by
  ext p
  constructor
  · rintro ⟨⟨_, hx⟩, ⟨ht, hy⟩⟩
    refine ⟨p.1, ht, Prod.ext rfl ?_⟩
    linarith [hx.1, hy.2]
  · rintro ⟨t, ht, rfl⟩
    change (L - (L - t) ∈ Icc (-d) d ∧ t ∈ Icc (L - (L - t)) (L - t)) ∧
      (t ∈ Icc (-d) d ∧ L - t ∈ Icc t (L - t))
    constructor
    · constructor
      · simpa only [sub_sub_cancel] using ht
      · constructor <;> linarith [ht.2]
    · exact ⟨ht, by constructor <;> linarith [ht.2]⟩

theorem trapezoid_inter_leftStrip {L d : ℝ} (hwidth : 2 * d < L) :
    trapezoid L d ∩ leftStrip L d =
      (fun t : ℝ => (t, t)) '' Icc (-d) d := by
  ext p
  constructor
  · rintro ⟨⟨ht, hx⟩, ⟨_, hy⟩⟩
    refine ⟨p.2, ht, Prod.ext ?_ rfl⟩
    linarith [hx.1, hy.1]
  · rintro ⟨t, ht, rfl⟩
    change (t ∈ Icc (-d) d ∧ t ∈ Icc t (L - t)) ∧
      (t ∈ Icc (-d) d ∧ t ∈ Icc t (L - t))
    have h : t ∈ Icc (-d) d ∧ t ∈ Icc t (L - t) :=
      ⟨ht, by constructor <;> linarith [ht.2]⟩
    exact ⟨h, h⟩

theorem disjoint_trapezoid_topStrip {L d : ℝ} (hwidth : 2 * d < L) :
    Disjoint (trapezoid L d) (topStrip L d) := by
  apply disjoint_left.mpr
  intro p hp hq
  linarith [hp.1.2, hq.1.2]

theorem disjoint_rightStrip_leftStrip {L d : ℝ} (hwidth : 2 * d < L) :
    Disjoint (rightStrip L d) (leftStrip L d) := by
  apply disjoint_left.mpr
  intro p hp hq
  linarith [hp.1.2, hq.1.2]

theorem union_four_strips {L d : ℝ} (hd : 0 ≤ d) (hwidth : 2 * d < L) :
    ((trapezoid L d ∪ rightStrip L d) ∪ topStrip L d) ∪ leftStrip L d =
      squareAnnulus L d := by
  classical
  have hL : 0 < L := by linarith
  ext p
  constructor
  · rintro (((hp | hp) | hp) | hp)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      · constructor <;> linarith [hp.1.1, hp.1.2]
      · intro h
        linarith [hp.1.2, h.2.1]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · constructor <;> linarith [hp.1.1, hp.1.2]
      · constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      · intro h
        linarith [hp.1.2, h.1.2]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      · constructor <;> linarith [hp.1.1, hp.1.2]
      · intro h
        linarith [hp.1.2, h.2.2]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · constructor <;> linarith [hp.1.1, hp.1.2]
      · constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      · intro h
        linarith [hp.1.2, h.1.1]
  · intro hp
    let a : Fin 4 → ℝ := ![p.2, L - p.1, L - p.2, p.1]
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image a Finset.univ_nonempty
    have h₀ : a i ≤ p.2 := hi 0 (Finset.mem_univ _)
    have h₁ : a i ≤ L - p.1 := hi 1 (Finset.mem_univ _)
    have h₂ : a i ≤ L - p.2 := hi 2 (Finset.mem_univ _)
    have h₃ : a i ≤ p.1 := hi 3 (Finset.mem_univ _)
    have hlow : -d ≤ a i := by
      fin_cases i <;> dsimp [a] <;>
        linarith [hp.1.1.1, hp.1.1.2, hp.1.2.1, hp.1.2.2]
    have hupp : a i ≤ d := by
      by_contra h
      have hlt : d < a i := lt_of_not_ge h
      apply hp.2
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    fin_cases i <;> dsimp [a] at hlow hupp h₀ h₁ h₂ h₃
    · exact Or.inl (Or.inl (Or.inl ⟨⟨hlow, hupp⟩, ⟨h₃, by linarith⟩⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨hlow, hupp⟩, ⟨h₀, by linarith⟩⟩))
    · exact Or.inl (Or.inr ⟨⟨hlow, hupp⟩, ⟨h₃, by linarith⟩⟩)
    · exact Or.inr ⟨⟨hlow, hupp⟩, ⟨h₀, by linarith⟩⟩

end PLAnnularStrip
