import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary

set_option autoImplicit false
open Set PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem closure_strict_marked_annulus :
    closure {z : P2 | -1 < depth 8 z ∧ depth 8 z < 1} = Ann := by
  let U : Set P2 :=
    (Ioo (-1) 9 ×ˢ Ioo (-1) 1) ∪ (Ioo (-1) 9 ×ˢ Ioo 7 9) ∪
      (Ioo (-1) 1 ×ˢ Ioo (-1) 9) ∪ (Ioo 7 9 ×ˢ Ioo (-1) 9)
  have hU : U = {z : P2 | -1 < depth 8 z ∧ depth 8 z < 1} := by
    ext z
    simp only [U,mem_union,mem_prod,mem_Ioo,mem_ofPred_eq,depth,lt_min_iff,
      min_lt_iff]
    constructor
    · rintro (((h | h) | h) | h) <;> rcases h with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      all_goals constructor
      all_goals first | exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩ |
        (first | exact Or.inl (Or.inr (by linarith)) |
          exact Or.inr (Or.inr (by linarith)) |
          exact Or.inl (Or.inl (by linarith)) |
          exact Or.inr (Or.inl (by linarith)))
    · rintro ⟨⟨⟨h1,h2⟩,⟨h3,h4⟩⟩,((h | h) | (h | h))⟩
      · exact Or.inl (Or.inr ⟨⟨h1,h⟩,⟨h2,by linarith⟩⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨⟨h1,by linarith⟩,⟨h2,h⟩⟩))
      · exact Or.inr ⟨⟨by linarith,by linarith⟩,⟨h2,by linarith⟩⟩
      · exact Or.inl (Or.inl (Or.inr ⟨⟨h1,by linarith⟩,⟨by linarith,by linarith⟩⟩))
  rw [←hU]
  simp only [U,closure_union,closure_prod_eq]
  norm_num only [closure_Ioo,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  ext z
  simp only [squareAnnulus,mem_union,mem_prod,mem_Icc,mem_sdiff,mem_Ioo]
  norm_num only [show (8 : ℝ) + 1 = 9 by norm_num,show (8 : ℝ) - 1 = 7 by norm_num]
  push Not
  constructor
  · rintro (((h | h) | h) | h) <;> rcases h with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    all_goals constructor
    all_goals first | exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩ |
      (rintro ⟨ha,hb⟩ hc; linarith)
  · rintro ⟨⟨⟨h1,h2⟩,⟨h3,h4⟩⟩,h⟩
    by_cases hx : z.1 ≤ 1
    · exact Or.inl (Or.inr ⟨⟨h1,hx⟩,h3,h4⟩)
    by_cases hx' : 7 ≤ z.1
    · exact Or.inr ⟨⟨hx',h2⟩,h3,h4⟩
    by_cases hy : z.2 ≤ 1
    · exact Or.inl (Or.inl (Or.inl ⟨⟨h1,h2⟩,h3,hy⟩))
    exact Or.inl (Or.inl (Or.inr ⟨⟨h1,h2⟩,h ⟨by linarith,by linarith⟩ (by linarith),h4⟩))

theorem image_marked_annulus_eq_closure_image_strict
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (p : P2 → X) (hp : ContinuousOn p Ann) :
    p '' Ann = closure (p '' {z | -1 < depth 8 z ∧ depth 8 z < 1}) := by
  have hcompact : IsCompact Ann :=
    (isCompact_Icc.prod isCompact_Icc).diff (isOpen_Ioo.prod isOpen_Ioo)
  apply Subset.antisymm
  · rw [←closure_strict_marked_annulus] at hp ⊢
    exact hp.image_closure
  · exact closure_minimal (image_mono (fun _ h =>
      mem_squareAnnulus_iff_depth.mpr ⟨h.1.le,h.2.le⟩))
      (hcompact.image_of_continuousOn hp).isClosed

theorem marked_annular_image_eq_frontier_closure
    {X : Type*} [TopologicalSpace X] [T2Space X] {D R : Set X}
    (p : P2 → X) (hp : ContinuousOn p Ann)
    (hfront : p '' Ann ⊆ frontier D)
    (hfull : frontier D ∩ interior R ⊆ p '' Ann)
    (hint : p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆ interior R)
    (hends : ∀ z : Ann, p z ∈ frontier R ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) :
    p '' Ann = closure (frontier D ∩ interior R) := by
  have hopen : p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} =
      frontier D ∩ interior R := by
    apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨hfront ⟨z,mem_squareAnnulus_iff_depth.mpr ⟨hz.1.le,hz.2.le⟩,rfl⟩,
        hint ⟨z,hz,rfl⟩⟩
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := hfull hx
      have hd := mem_squareAnnulus_iff_depth.mp hz
      have hne : depth 8 z ≠ -1 ∧ depth 8 z ≠ 1 := by
        constructor <;> intro hh
        all_goals exact ((hends ⟨z,hz⟩).mpr (by tauto)).2 hx.2
      exact ⟨z,⟨lt_of_le_of_ne hd.1 hne.1.symm,lt_of_le_of_ne hd.2 hne.2⟩,rfl⟩
  have hcompact : IsCompact Ann :=
    (isCompact_Icc.prod isCompact_Icc).diff (isOpen_Ioo.prod isOpen_Ioo)
  apply Subset.antisymm
  · rw [←closure_strict_marked_annulus] at hp ⊢
    exact hp.image_closure.trans (closure_mono hopen.subset)
  · exact closure_minimal hfull (hcompact.image_of_continuousOn hp).isClosed

end PoincareConjecture.M76
