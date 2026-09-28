import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry
import PoincareConjecture.Proofs.M76.Mathlib.CubeSectorSubdivision










set_option autoImplicit false

open Set Metric Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsCompact.exists_finite_convex_neighborhood {S : Set E} (hS : IsCompact S) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
      S ⊆ interior K.space := by
  classical
  let ι := Fin (Module.finrank ℝ E)
  let c : E ≃L[ℝ] (ι → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [ι])
  obtain ⟨R, hR, hbound⟩ := (hS.image c.continuous).isBounded.exists_pos_norm_lt
  let C : Set E := c ⁻¹' closedBall (0 : ι → ℝ) R
  have hC : IsCompact C := c.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hcv : Convex ℝ C := (convex_closedBall (0 : ι → ℝ) R).linear_preimage c.toLinearMap
  have hSC : S ⊆ interior C := by
    intro x hx
    change x ∈ interior (c.toHomeomorph ⁻¹' closedBall (0 : ι → ℝ) R)
    rw [← c.toHomeomorph.preimage_interior]
    apply ball_subset_interior_closedBall
    change c x ∈ ball (0 : ι → ℝ) R
    rw [mem_ball, dist_zero_right]
    exact hbound (c x) (mem_image_of_mem c hx)
  let A : ι ⊕ ι → E →ᵃ[ℝ] ℝ := fun i =>
    ((signedCubeCoordinate i).comp c.toLinearMap).toAffineMap - AffineMap.const ℝ E R
  let H := Finset.univ.image A
  have hrep : C = {x | ∀ a ∈ H, a x ≤ 0} := by
    ext x
    change dist (c x) 0 ≤ R ↔ ∀ a ∈ H, a x ≤ 0
    rw [dist_zero_right]
    constructor
    · intro hx a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      change signedCubeCoordinate i (c x) - R ≤ 0
      exact sub_nonpos.mpr ((signedCubeCoordinate_le_norm i (c x)).trans hx)
    · intro hx
      apply (pi_norm_le_iff_of_nonneg hR.le).mpr
      intro i
      have hp : c x i - R ≤ 0 := hx (A (.inl i)) (Finset.mem_image.mpr ⟨.inl i, by simp, rfl⟩)
      have hn : -(c x i) - R ≤ 0 := hx (A (.inr i)) (Finset.mem_image.mpr ⟨.inr i, by simp, rfl⟩)
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨K, hK, hKC⟩ := hC.exists_finite_triangulation_of_halfspaces H hrep
  exact ⟨K, hK, hKC.symm ▸ hcv, hKC.symm ▸ hSC⟩

end Set
