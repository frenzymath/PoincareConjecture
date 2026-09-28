import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set Geometry

namespace Set

theorem isFinitePLBallPair_Icc {a b : ℝ} (hab : a < b) :
    IsFinitePLBallPair ℝ (Icc a b) {a, b} := by
  classical
  let H : Finset (ℝ →ᵃ[ℝ] ℝ) :=
    {AffineMap.const ℝ ℝ a - AffineMap.id ℝ ℝ,
      AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ b}
  have hrep : Icc a b = {x | ∀ A ∈ H, A x ≤ 0} := by
    ext x
    simp [H]
  obtain ⟨K, hK, hKs⟩ := isCompact_Icc.exists_finite_triangulation_of_halfspaces H hrep
  rw [← frontier_Icc hab.le]
  exact isFinitePLBallPair_of_compact_convex isCompact_Icc (convex_Icc a b)
    (by rw [interior_Icc]; exact nonempty_Ioo.mpr hab) K hK hKs

theorem isFinitePLBallPair_affine_interval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b : ℝ} (hab : a < b) (f : ℝ →ᴬ[ℝ] E) (hf : InjOn f (Icc a b)) :
    IsFinitePLBallPair ℝ (f '' Icc a b) {f a, f b} := by
  simpa only [image_pair] using (isFinitePLBallPair_Icc hab).affine_image f hf

end Set
