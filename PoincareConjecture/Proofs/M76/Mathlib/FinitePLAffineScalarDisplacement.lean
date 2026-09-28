import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.scalar_of_affine_displacement
    {f : E → F} {g : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (A : F →ᴬ[ℝ] ℝ) (B : E →ᴬ[ℝ] ℝ) {k : ℝ} (hk : k ≠ 0)
    (hval : ∀ x ∈ S, A (f x) = B x + k * g x) : FinitePiecewiseAffineOn g S := by
  obtain ⟨K, hK, hspace, hfaces⟩ := hf
  refine ⟨K, hK, hspace, fun s hs => ?_⟩
  obtain ⟨a, ha⟩ := hfaces s hs
  refine ⟨k⁻¹ • (A.comp a - B), fun x hx => ?_⟩
  have hxS : x ∈ S := hspace ▸ K.convexHull_subset_space hs hx
  have heq : A (a x) - B x = k * g x := by
    rw [← ha hx]
    linarith [hval x hxS]
  change g x = k⁻¹ * (A (a x) - B x)
  rw [heq, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

end Geometry
