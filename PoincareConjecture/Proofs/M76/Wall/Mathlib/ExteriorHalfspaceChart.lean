import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts










set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph





theorem exterior_halfspace_and_frontier
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : OpenPartialHomeomorph X E) {C L : Set X}
    (hsource : B.source ⊆ interior C)
    (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hhalf : ∀ x ∈ B.source, x ∈ L ↔ 0 ≤ ell (B x)) :
    (∀ x ∈ B.source, x ∈ C \ interior L ↔ 0 ≤ (-ell) (B x)) ∧
      ∀ x ∈ B.source, x ∈ frontier (C \ interior L) ↔ x ∈ frontier L := by
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hInt : interior {z | 0 ≤ ell z} = {z | 0 < ell z} := by
    change interior ((ell : E → ℝ) ⁻¹' Ici 0) = (ell : E → ℝ) ⁻¹' Ioi 0
    rw [← hopen.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici]
  have himage : B.IsImage L {z | 0 ≤ ell z} := fun {x} hx => (hhalf x hx).symm
  have hinterior (x : X) (hx : x ∈ B.source) :
      x ∈ interior L ↔ 0 < ell (B x) := by
    have h := himage.interior.apply_mem_iff hx
    rw [hInt] at h
    exact h.symm
  have hext (x : X) (hx : x ∈ B.source) :
      x ∈ C \ interior L ↔ 0 ≤ (-ell) (B x) := by
    change (x ∈ C ∧ x ∉ interior L) ↔ 0 ≤ -ell (B x)
    rw [hinterior x hx, not_lt, neg_nonneg]
    exact and_iff_right (interior_subset (hsource hx))
  have hneg : (-ell).toAffineMap.linear ≠ 0 := by
    change -ell.toAffineMap.linear ≠ 0
    exact neg_ne_zero.mpr hell
  refine ⟨hext, ?_⟩
  intro x hx
  have hfront := (B.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff hx
  have hextfront :=
    (B.isImage_frontier_of_affine_nonneg (-ell) hneg hext).apply_mem_iff hx
  change -ell (B x) = 0 ↔ x ∈ frontier (C \ interior L) at hextfront
  change ell (B x) = 0 ↔ x ∈ frontier L at hfront
  exact hextfront.symm.trans ((neg_eq_zero).trans hfront)

end OpenPartialHomeomorph
