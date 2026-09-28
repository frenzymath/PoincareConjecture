import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedIncidence

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.restricted_collar_zero_subset
    {S TY b : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hTY : TY ⊆ M.collar)
    (hY : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (M.chart p : E) ∈ TY → (p : E × ℝ).1 ∈ b) :
    TY ∩ {x | A x = 0} ⊆ b := by
  intro x hx
  let p := M.chart.symm ⟨x, hTY hx.1⟩
  have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
  have hz : (p : E × ℝ).2 = 0 := (M.height p).symm.trans ((congrArg A hp).trans hx.2)
  have hpx : (p : E × ℝ).1 = x := (M.bottom p hz).symm.trans hp
  exact hpx ▸ hY p (hp.symm ▸ hx.1)

theorem AlexanderCollarSlab.selected_image_closed_slab_eq
    {S s d TX TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hs : s ⊆ S)
    (hsplit : M.collar ∩ s = TX ∪ TY) (hd : d ⊆ {x | A x = 0})
    (H : E ≃ₜ E) (hraise : ∀ x, A x ≤ A (H x))
    (hneg : ∀ x ∈ s, A x < 0 → H x = x)
    (hhigh : ∀ x, β ≤ A x → H x = x)
    (hR : ∀ x ∈ M.residual, H x = x) :
    (H '' TX) ∪ ((M.residual ∩ s) ∪ (H '' (TY ∪ d))) =
      (H '' (s ∪ d)) ∩ {x | A x ∈ Icc 0 β} := by
  have hT : M.collar ⊆ S ∩ {x | A x ∈ Icc 0 β} :=
    subset_union_left.trans M.cover.subset
  have hres : M.residual ⊆ S ∩ {x | A x ∈ Icc 0 β} :=
    subset_union_right.trans M.cover.subset
  have hX : TX ⊆ M.collar ∩ s := subset_union_left.trans hsplit.symm.subset
  have hY : TY ⊆ M.collar ∩ s := subset_union_right.trans hsplit.symm.subset
  have hband (x : E) (hx : A x ∈ Icc 0 β) : A (H x) ∈ Icc 0 β := by
    refine ⟨hx.1.trans (hraise x), ?_⟩
    by_contra hn
    have hy : β ≤ A (H x) := (lt_of_not_ge hn).le
    have heq : H x = x := H.injective (hhigh (H x) hy)
    exact (not_le_of_gt (lt_of_not_ge hn)) (heq.symm ▸ hx.2)
  ext y
  constructor
  · rintro (hyX | hyR | hyY)
    · obtain ⟨x, hx, rfl⟩ := hyX
      exact ⟨⟨x, Or.inl (hX hx).2, rfl⟩, hband x (hT (hX hx).1).2⟩
    · exact ⟨⟨y, Or.inl hyR.2, hR y hyR.1⟩, (hres hyR.1).2⟩
    · obtain ⟨x, hx | hx, rfl⟩ := hyY
      · exact ⟨⟨x, Or.inl (hY hx).2, rfl⟩, hband x (hT (hY hx).1).2⟩
      · have hxA : A x = 0 := hd hx
        exact ⟨⟨x, Or.inr hx, rfl⟩, hband x (by rw [hxA]; exact ⟨le_rfl, M.width_pos.le⟩)⟩
  · rintro ⟨⟨x, hx | hx, rfl⟩, hxA⟩
    · have hxnonneg : 0 ≤ A x := by
        by_contra hn
        have hfix := hneg x hx (lt_of_not_ge hn)
        rw [hfix] at hxA
        exact hn hxA.1
      have hxupper : A x ≤ β := (hraise x).trans hxA.2
      rcases M.cover.symm.subset ⟨hs hx, hxnonneg, hxupper⟩ with hxT | hxR
      · rcases hsplit.subset ⟨hxT, hx⟩ with hxX | hxY
        · exact Or.inl ⟨x, hxX, rfl⟩
        · exact Or.inr (Or.inr ⟨x, Or.inl hxY, rfl⟩)
      · exact Or.inr (Or.inl ((hR x hxR).symm ▸ And.intro hxR hx))
    · exact Or.inr (Or.inr ⟨x, Or.inr hx, rfl⟩)

theorem AlexanderCollarSlab.selected_residual_zero_subset
    {S s d TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hTY : TY ⊆ M.collar)
    (hTYzero : TY ∩ {x | A x = 0} ⊆ d)
    (H : E ≃ₜ E) (hraise : ∀ x, A x ≤ A (H x))
    (hcapzero : (H '' d) ∩ {x | A x = 0} ⊆ {q}) :
    ((M.residual ∩ s) ∪ (H '' (TY ∪ d))) ∩ {x | A x = 0} ⊆ {q} := by
  intro y hy
  rcases hy.1 with hyR | hyimage
  · exact M.residual_zero ⟨hyR.1, hy.2⟩
  · obtain ⟨x, hx | hx, hxy⟩ := hyimage
    · have hxnonneg : 0 ≤ A x := (M.cover.subset (Or.inl (hTY hx))).2.1
      have hxzero : A x = 0 := le_antisymm
        ((hraise x).trans_eq ((congrArg A hxy).trans hy.2)) hxnonneg
      exact hcapzero ⟨⟨x, hTYzero ⟨hx, hxzero⟩, hxy⟩, hy.2⟩
    · exact hcapzero ⟨⟨x, hx, hxy⟩, hy.2⟩

end Geometry
