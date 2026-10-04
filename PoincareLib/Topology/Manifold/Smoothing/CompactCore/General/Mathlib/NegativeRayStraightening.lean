import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.Mathlib.TwoHalfspaceShear

/-!
# Straightening a negative ray while fixing the whole zero plane

The negative correction comes from the actual ray direction and
the slope-one normal. The positive correction is zero, so the full
zero plane and the original height are retained pointwise.
See Wall011, section4.
-/

set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap

/-- A genuinely negative ray has a global PL straightener preserving
the entire linear height and fixing the whole zero plane. Its exact
normal-ray formula holds for every nonnegative parameter.
See Wall011, section4. -/
theorem exists_negative_ray_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ell : E →L[ℝ] ℝ) (v d : E) (hv : ell v = 1) (hd : ell d < 0) :
    ∃ H : E ≃ₜ E, H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ x, ell (H x) = ell x) ∧ (∀ x, ell x = 0 → H x = x) ∧
      ∀ t : ℝ, 0 ≤ t → H (t • d) = (t * ell d) • v := by
  let k : E := (ell d)⁻¹ • d - v
  have hk : ell k = 0 := by
    simp only [k, map_sub, map_smul, hv, smul_eq_mul, inv_mul_cancel₀ hd.ne, sub_self]
  obtain ⟨H, hPL, hH, _, hheight⟩ :=
    ell.exists_two_halfspace_shear k 0 hk (map_zero ell)
  refine ⟨H, hPL, hheight, ?_, ?_⟩
  · intro x hx
    rw [hH, hx, min_self, max_self, zero_smul, zero_smul, sub_zero, sub_zero]
  · intro t ht
    have htd : t * ell d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hd.le
    rw [hH, map_smul, smul_eq_mul, min_eq_left htd, smul_zero, sub_zero]
    dsimp only [k]
    rw [smul_sub, smul_smul]
    have hcancel : (t * ell d) * (ell d)⁻¹ = t := by
      rw [mul_assoc, mul_inv_cancel₀ hd.ne, mul_one]
    rw [hcancel]
    abel

end ContinuousLinearMap
