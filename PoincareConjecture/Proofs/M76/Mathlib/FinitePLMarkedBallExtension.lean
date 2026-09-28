import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing










set_option autoImplicit false

open Set Geometry

namespace Set

variable {V W X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]





theorem IsFinitePLBallPair.exists_extension_of_boundary_piece
    {s b d c : Set X} {t B D C : Set Y}
    (hs : IsFinitePLBallPair V s (b ∪ d)) (ht : IsFinitePLBallPair V t (B ∪ D))
    (hb : IsFinitePLBallPair W b c) (hB : IsFinitePLBallPair W B C)
    (hinter : b ∩ d = c) (hInter : B ∩ D = C)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hmem : ∀ x : d, (x : X) ∈ c ↔ (e x : Y) ∈ C) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : d, H ⟨x, hs.1 (Or.inr x.property)⟩ =
        ⟨e x, ht.1 (Or.inr (e x).property)⟩) ∧
      (∀ x : s, (x : X) ∈ b ↔ (H x : Y) ∈ B) ∧
      (∀ x : s, (x : X) ∈ d ↔ (H x : Y) ∈ D) := by
  obtain ⟨E, hE, hEd, hEbmem, hEdmem⟩ :=
    hb.exists_union_homeomorph_of_boundary_piece hB hinter hInter e he hmem
  obtain ⟨H, hH, hHE, hHmem⟩ := hs.exists_extension ht E hE
  have hHd (x : d) : H ⟨x, hs.1 (Or.inr x.property)⟩ =
      ⟨e x, ht.1 (Or.inr (e x).property)⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : t => (y : Y)) (hHE ⟨x, Or.inr x.property⟩)).trans
      (congrArg (fun y : (B ∪ D : Set Y) => (y : Y)) (hEd x))
  have hpiece (a : Set X) (A : Set Y) (ha : a ⊆ b ∪ d) (hA : A ⊆ B ∪ D)
      (hEa : ∀ x : (b ∪ d : Set X), (x : X) ∈ a ↔ (E x : Y) ∈ A) (x : s) :
      (x : X) ∈ a ↔ (H x : Y) ∈ A := by
    constructor
    · intro hx
      have hv := congrArg (fun y : t => (y : Y)) (hHE ⟨x, ha hx⟩)
      rw [hv]
      exact (hEa ⟨x, ha hx⟩).mp hx
    · intro hx
      have hxb := (hHmem x).mpr (hA hx)
      have hv := congrArg (fun y : t => (y : Y)) (hHE ⟨x, hxb⟩)
      exact (hEa ⟨x, hxb⟩).mpr (hv ▸ hx)
  exact ⟨H, hH, hHd,
    hpiece b B subset_union_left subset_union_left hEbmem,
    hpiece d D subset_union_right subset_union_right hEdmem⟩

end Set
