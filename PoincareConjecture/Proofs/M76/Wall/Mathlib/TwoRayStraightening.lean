import PoincareConjecture.Proofs.M76.Wall.Mathlib.TwoHalfspaceShear

set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap

theorem exists_two_ray_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ell : E →L[ℝ] ℝ) (u v : E) (hu : ell u < 0) (hv : 0 < ell v) :
    ∃ w : E, ell w = 1 ∧ ∃ H : E ≃ₜ E,
      H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧ H 0 = 0 ∧
      (∀ x, ell (H x) = ell x) ∧
      (∀ t : ℝ, 0 ≤ t → H (t • u) = (t * ell u) • w) ∧
      ∀ t : ℝ, 0 ≤ t → H (t • v) = (t * ell v) • w := by
  let w : E := (ell v)⁻¹ • v
  have hu0 : ell u ≠ 0 := ne_of_lt hu
  have hv0 : ell v ≠ 0 := ne_of_gt hv
  have hw : ell w = 1 := by
    simp only [w, map_smul, smul_eq_mul, inv_mul_cancel₀ hv0]
  let a : E := (ell u)⁻¹ • u - w
  let b : E := (ell v)⁻¹ • v - w
  have ha : ell a = 0 := by
    simp only [a, map_sub, map_smul, smul_eq_mul, hw, inv_mul_cancel₀ hu0, sub_self]
  have hb : ell b = 0 := by
    simp only [b, map_sub, map_smul, smul_eq_mul, hw, inv_mul_cancel₀ hv0, sub_self]
  obtain ⟨H, hPL, hH, _, hheight⟩ := ell.exists_two_halfspace_shear a b ha hb
  refine ⟨w, hw, H, hPL, ?_, hheight, ?_, ?_⟩
  · simp only [hH, map_zero, min_self, max_self, zero_smul, sub_zero]
  · intro t ht
    have htu : ell (t • u) ≤ 0 := by
      simpa only [map_smul, smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos ht hu.le
    rw [hH, min_eq_left htu, max_eq_right htu, zero_smul, sub_zero]
    simp only [map_smul, smul_eq_mul]
    change t • u - (t * ell u) • ((ell u)⁻¹ • u - w) = (t * ell u) • w
    rw [smul_sub, smul_smul, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
    abel
  · intro t ht
    have htv : 0 ≤ ell (t • v) := by
      simpa only [map_smul, smul_eq_mul] using mul_nonneg ht hv.le
    rw [hH, min_eq_right htv, max_eq_left htv, zero_smul, sub_zero]
    simp only [map_smul, smul_eq_mul]
    change t • v - (t * ell v) • ((ell v)⁻¹ • v - w) = (t * ell v) • w
    rw [smul_sub, smul_smul, mul_assoc, mul_inv_cancel₀ hv0, mul_one]
    abel

end ContinuousLinearMap
