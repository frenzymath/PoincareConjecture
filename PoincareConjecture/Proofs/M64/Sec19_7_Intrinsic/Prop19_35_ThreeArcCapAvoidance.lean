import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCornerCaps

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_three_arc_cap_avoidance
    {alpha beta sigma : ℝ → AnnulusCoordinates} (hs : Continuous sigma)
    {A B T r0 r1 : ℝ} (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hr0 : r0 ≤ min A T / 3) (hr1 : r1 ≤ min B T / 3)
    (hend : alpha A = beta 0)
    (hab : ∀ x ∈ Icc 0 A, ∀ y ∈ Icc 0 B,
      alpha x = beta y → x = A ∧ y = 0)
    (has : ∀ x ∈ Icc 0 A, ∀ y ∈ Icc 0 T,
      alpha x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 B, ∀ y ∈ Icc 0 T,
      beta x = sigma y → x = B ∧ y = T)
    {U D0 D1 : Set AnnulusCoordinates}
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ sigma '' Icc 0 T)
    (hD0 : IsCompact D0) (hD1 : IsCompact D1)
    (hcontact0 : D0 ∩ frontier U ⊆ alpha '' Icc 0 r0 ∪ sigma '' Icc 0 r0)
    (hcontact1 : D1 ∩ frontier U ⊆
      (fun s => beta (B - s)) '' Icc 0 r1 ∪
      (fun s => sigma (T - s)) '' Icc 0 r1) :
    Disjoint D0 (beta '' Icc 0 B) ∧ Disjoint D1 (alpha '' Icc 0 A) ∧
      IsOpen (D0 ∪ D1 ∪ sigma '' Icc 0 T)ᶜ ∧
      alpha A ∈ (D0 ∪ D1 ∪ sigma '' Icc 0 T)ᶜ := by
  have hr0A : r0 < A := by
    have := hr0.trans (div_le_div_of_nonneg_right (min_le_left A T) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hr0T : r0 < T := by
    have := hr0.trans (div_le_div_of_nonneg_right (min_le_right A T) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hr1B : r1 < B := by
    have := hr1.trans (div_le_div_of_nonneg_right (min_le_left B T) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hr1T : r1 < T := by
    have := hr1.trans (div_le_div_of_nonneg_right (min_le_right B T) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hsep0 : Disjoint D0 (beta '' Icc 0 B) := by
    apply disjoint_left.mpr
    rintro _ hp ⟨y, hy, rfl⟩
    have hyf : beta y ∈ frontier U := hfront ▸ Or.inl (Or.inr ⟨y, hy, rfl⟩)
    rcases hcontact0 ⟨hp, hyf⟩ with h | h
    · obtain ⟨x, hx, he⟩ := h
      have := (hab x ⟨hx.1, hx.2.trans hr0A.le⟩ y hy he).1
      linarith [hx.2]
    · obtain ⟨x, hx, he⟩ := h
      have := (hbs y hy x ⟨hx.1, hx.2.trans hr0T.le⟩ he.symm).2
      linarith [hx.2]
  have hsep1 : Disjoint D1 (alpha '' Icc 0 A) := by
    apply disjoint_left.mpr
    rintro _ hp ⟨x, hx, rfl⟩
    have hxf : alpha x ∈ frontier U := hfront ▸ Or.inl (Or.inl ⟨x, hx, rfl⟩)
    rcases hcontact1 ⟨hp, hxf⟩ with h | h
    · obtain ⟨s, hs, he⟩ := h
      have hBs : B - s ∈ Icc (0 : ℝ) B := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have := (hab x hx (B - s) hBs he.symm).2
      linarith [hs.2]
    · obtain ⟨s, hs, he⟩ := h
      have hTs : T - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have := (has x hx (T - s) hTs he.symm).2
      linarith [hs.2]
  refine ⟨hsep0, hsep1,
    ((hD0.union hD1).union (isCompact_Icc.image hs)).isClosed.isOpen_compl, ?_⟩
  rintro ((hp | hp) | hp)
  · exact disjoint_left.mp hsep0 hp ⟨0, ⟨le_rfl, hB.le⟩, hend.symm⟩
  · exact disjoint_left.mp hsep1 hp ⟨A, ⟨hA.le, le_rfl⟩, rfl⟩
  · obtain ⟨s, hs, he⟩ := hp
    exact hA.ne' (has A ⟨hA.le, le_rfl⟩ s hs he.symm).1

end PoincareConjecture
