import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem height_directional_displacement (A : E →ᵃ[ℝ] ℝ)
    {v : E} (hv : A.linear v = 1) (t a : ℝ) (x : E) :
    A (x + (t * a) • v) = t * a + A x := by
  rw [add_comm x]
  change A ((t * a) • v +ᵥ x) = t * a + A x
  rw [A.map_vadd, map_smul, hv]
  change t * a * 1 + A x = t * a + A x
  rw [mul_one]

theorem directional_scalar_eq_zero_of_fixed (A : E →ᵃ[ℝ] ℝ)
    {v x : E} (hv : A.linear v = 1) {t a : ℝ} (ht : t ≠ 0)
    (hfix : x + (t * a) • v = x) : a = 0 := by
  have h := A.height_directional_displacement hv t a x
  rw [hfix] at h
  have hmul : t * a = 0 := add_right_cancel (h.symm.trans (zero_add (A x)).symm)
  exact (mul_eq_zero.mp hmul).resolve_left ht

end AffineMap

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.directional_scalar
    {f : E → E} {g : E → ℝ} {s : Set E}
    (hf : FinitePiecewiseAffineOn f s) (A : E →ᵃ[ℝ] ℝ)
    {v : E} (hv : A.linear v = 1) {t : ℝ} (ht : t ≠ 0)
    (hformula : ∀ x ∈ s, f x = x + (t * g x) • v) :
    FinitePiecewiseAffineOn g s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  let B : E →ᴬ[ℝ] ℝ := ⟨A, A.continuous_of_finiteDimensional⟩
  refine ⟨K, hK, rfl, fun r hr => ?_⟩
  obtain ⟨L, hL⟩ := hfaces r hr
  refine ⟨t⁻¹ • (B.comp L - B), fun x hx => ?_⟩
  change g x = t⁻¹ * (A (L x) - A x)
  rw [← hL hx, hformula x (SimplicialComplex.convexHull_subset_space hr hx),
    A.height_directional_displacement hv, add_sub_cancel_right]
  rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]

end Geometry
