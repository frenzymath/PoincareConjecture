import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem interior_preimage_convex (a : F →ᴬ[ℝ] E) {s : Set E} (hcv : Convex ℝ s)
    (hne : ∃ y, a y ∈ interior s) : interior (a ⁻¹' s) = a ⁻¹' interior s := by
  apply Subset.antisymm _ (preimage_interior_subset_interior_preimage a.continuous)
  intro x hx
  by_contra hnot
  obtain ⟨y, hy⟩ := hne
  obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hcv.interior isOpen_interior hnot
  have hle : ∀ z ∈ s, L z ≤ L (a x) := by
    intro z hz
    apply le_on_closure (fun w hw => (hL w hw).le)
      L.continuous.continuousOn continuousOn_const
    rw [hcv.closure_interior_eq_closure_of_nonempty_interior ⟨a y, hy⟩]
    exact subset_closure hz
  let A : F →ᵃ[ℝ] ℝ := L.toLinearMap.toAffineMap.comp a.toAffineMap -
    AffineMap.const ℝ F (L (a x))
  have hAx : A x = 0 := sub_self _
  have hAy : A y < 0 := sub_neg.mpr (hL (a y) hy)
  have hA : A.linear ≠ 0 := by
    intro hzero
    have h := A.linearMap_vsub y x
    change A.linear (y - x) = A y - A x at h
    rw [hzero, LinearMap.zero_apply, hAx, sub_zero] at h
    linarith
  have hsub : a ⁻¹' s ⊆ {z | A z ≤ 0} := fun z hz => sub_nonpos.mpr (hle (a z) hz)
  have hxi := interior_mono hsub hx
  rw [A.interior_nonpos hA] at hxi
  change A x < 0 at hxi
  exact (hAx ▸ hxi).false

theorem frontier_preimage_convex (a : F →ᴬ[ℝ] E) {s : Set E}
    (hs : IsClosed s) (hcv : Convex ℝ s) (hne : ∃ y, a y ∈ interior s) :
    frontier (a ⁻¹' s) = a ⁻¹' frontier s := by
  rw [frontier, (hs.preimage a.continuous).closure_eq, a.interior_preimage_convex hcv hne,
    frontier, hs.closure_eq, preimage_sdiff]

end ContinuousAffineMap
