import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCornerCaps
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapGeometry

noncomputable section
set_option autoImplicit false

open Set

namespace PoincareConjecture

theorem m64Intrinsic_triangle_caps_avoid_opposite_arcs
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    {U : Set AnnulusCoordinates} (C : M64IntrinsicTriangleCaps base alpha beta D A B U)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    Disjoint (C.carrier 0) (beta '' Icc 0 B) ∧
      Disjoint (C.carrier 1) (alpha '' Icc 0 A) ∧
      Disjoint (C.carrier 2) (base '' Icc 0 D) := by
  have h0D : C.radius 0 < D := C.radius_lt_left 0
  have h0A : C.radius 0 < A := C.radius_lt_right 0
  have h1D : C.radius 1 < D := C.radius_lt_left 1
  have h1B : C.radius 1 < B := C.radius_lt_right 1
  have h2A : C.radius 2 < A := C.radius_lt_left 2
  have h2B : C.radius 2 < B := C.radius_lt_right 2
  refine ⟨disjoint_left.mpr ?_, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · rintro _ hp ⟨t, ht, rfl⟩
    have hpf : beta t ∈ frontier U := hfront ▸ Or.inr (Or.inr ⟨t, ht, rfl⟩)
    rcases (C.frontier_contact 0).subset ⟨hp, hpf⟩ with h | h
    · obtain ⟨s, hs, heq⟩ := h
      have he := (hbaseB s ⟨hs.1, hs.2.trans h0D.le⟩ t ht heq).1
      linarith only [he, hs.2, h0D]
    · obtain ⟨s, hs, heq⟩ := h
      have he := (hsides s ⟨hs.1, hs.2.trans h0A.le⟩ t ht heq).1
      linarith only [he, hs.2, h0A]
  · rintro _ hp ⟨t, ht, rfl⟩
    have hpf : alpha t ∈ frontier U := hfront ▸ Or.inr (Or.inl ⟨t, ht, rfl⟩)
    rcases (C.frontier_contact 1).subset ⟨hp, hpf⟩ with h | h
    · obtain ⟨s, hs, heq⟩ := h
      have hDs : D - s ∈ Icc 0 D :=
        ⟨by linarith only [hs.2, h1D], by linarith only [hs.1]⟩
      have he := (hbaseA (D - s) hDs t ht heq).1
      linarith only [he, hs.2, h1D]
    · obtain ⟨s, hs, heq⟩ := h
      have he := (hsides t ht s ⟨hs.1, hs.2.trans h1B.le⟩ heq.symm).2
      linarith only [he, hs.2, h1B]
  · rintro _ hp ⟨t, ht, rfl⟩
    have hpf : base t ∈ frontier U := hfront ▸ Or.inl ⟨t, ht, rfl⟩
    rcases (C.frontier_contact 2).subset ⟨hp, hpf⟩ with h | h
    · obtain ⟨s, hs, heq⟩ := h
      have hAs : A - s ∈ Icc 0 A :=
        ⟨by linarith only [hs.2, h2A], by linarith only [hs.1]⟩
      have he := (hbaseA t ht (A - s) hAs heq.symm).2
      linarith only [he, hs.2, h2A]
    · obtain ⟨s, hs, heq⟩ := h
      have hBs : B - s ∈ Icc 0 B :=
        ⟨by linarith only [hs.2, h2B], by linarith only [hs.1]⟩
      have he := (hbaseB t ht (B - s) hBs heq.symm).2
      linarith only [he, hs.2, h2B]

end PoincareConjecture
