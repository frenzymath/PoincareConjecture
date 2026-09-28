import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set Geometry Metric

namespace Set

theorem isFinitePLBallPair_unit_cube {ι : Type*} [Fintype ι] :
    IsFinitePLBallPair (ι → ℝ) (closedBall (0 : ι → ℝ) 1)
      (sphere (0 : ι → ℝ) 1) := by
  classical
  let A : ι ⊕ ι → (ι → ℝ) →ᵃ[ℝ] ℝ := fun i =>
    (signedCubeCoordinate i).toAffineMap - AffineMap.const ℝ (ι → ℝ) 1
  let H := Finset.univ.image A
  have hrep : closedBall (0 : ι → ℝ) 1 = {x | ∀ a ∈ H, a x ≤ 0} := by
    rw [closedBall_eq_signedCube_halfspaces]
    ext x
    constructor
    · intro hx a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      change signedCubeCoordinate i x - 1 ≤ 0
      exact sub_nonpos.mpr (hx i)
    · intro hx i
      have h := hx (A i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      exact sub_nonpos.mp h
  have hball := isFinitePLBallPair_of_affine_halfspaces (isCompact_closedBall _ _) H hrep
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
  simpa only [frontier_closedBall _ one_ne_zero] using hball

end Set
