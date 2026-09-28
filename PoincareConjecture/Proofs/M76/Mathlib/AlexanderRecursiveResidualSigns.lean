import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveClosedPieces
import PoincareConjecture.Proofs.M76.Mathlib.ClosedComplementHeightSigns

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.fixed_residual_mem_both_height_closures
    {S s s' d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {x | A x = 0})
    (H : E ≃ₜ E) (hfix : ∀ x ∈ M.residual, H x = x)
    {x : E} (hx : x ∈ M.residual ∩ s) (hxT : x ∉ M.collar)
    (hxA : A x ∈ Ioo (0 : ℝ) β)
    (hlo : x ∈ closure (S ∩ {y | A y < A x}))
    (hhi : x ∈ closure (S ∩ {y | A x < A y})) :
    x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hT : IsClosed M.collar :=
    (M.isCompact_piece_of_closed_base isClosed_univ Subset.rfl
      (fun p => iff_of_true (M.chart p).property (mem_univ _))).isClosed
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hRS : M.residual ⊆ S :=
    (subset_union_right.trans M.cover.subset).trans inter_subset_left
  let Z := (M.collar ∪ s') ∩ {y | A y ∈ Icc (0 : ℝ) β}
  have hZ : IsClosed Z := (hT.union hs').inter
    (isClosed_Icc.preimage A.continuous_of_finiteDimensional)
  have hcover : ((M.residual ∩ s) ∩ {y | A y ∈ Icc (0 : ℝ) β}) ∪ Z =
      S ∩ {y | A y ∈ Icc (0 : ℝ) β} := by
    ext y
    constructor
    · rintro (⟨hyR, hyA⟩ | ⟨hyT | hys', hyA⟩)
      · exact ⟨hRS hyR.1, hyA⟩
      · exact ⟨hTS hyT, hyA⟩
      · exact ⟨hunion.subset (Or.inr hys'), hyA⟩
    · intro hy
      rcases M.cover.symm.subset hy with hyT | hyR
      · exact Or.inr ⟨Or.inl hyT, hy.2⟩
      · rcases hunion.symm.subset hy.1 with hys | hys'
        · exact Or.inl ⟨⟨hyR, hys⟩, hy.2⟩
        · exact Or.inr ⟨Or.inr hys', hy.2⟩
  have hxZ : x ∉ Z := by
    rintro ⟨hxT' | hxs', _⟩
    · exact hxT hxT'
    · exact hxA.1.ne' (hcut ⟨hx.2, hxs'⟩)
  let e := Homeomorph.refl (M.residual ∩ s : Set E)
  have hsigns := e.mem_both_height_closures_of_closed_band_cover
      A A A.continuous_of_finiteDimensional
      (fun _ => rfl) hZ hcover ⟨x, hx⟩ hxZ hxA.1 hxA.2 hlo hhi
  have htarget : M.residual ∩ s ⊆ H '' (s ∪ d) :=
    fun y hy => ⟨y, Or.inl hy.2, hfix y hy.1⟩
  exact ⟨closure_mono (inter_subset_inter_left _ htarget) hsigns.1,
    closure_mono (inter_subset_inter_left _ htarget) hsigns.2⟩

end Geometry
