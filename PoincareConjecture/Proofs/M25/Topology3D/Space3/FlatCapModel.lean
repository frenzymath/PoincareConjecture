import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCapProfile

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (a : ℝ → ℝ) (b : E → ℝ)
variable (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
variable (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)

noncomputable def flatCapDiffeomorph :
    Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
  ((ContinuousLinearEquiv.prodComm ℝ E ℝ).toDiffeomorph.trans
    (fiberScalingDiffeomorph a ha ha0)).trans
      ((ContinuousLinearEquiv.prodComm ℝ ℝ E).toDiffeomorph.trans
        (fiberScalingDiffeomorph b hb hb0))

@[simp] theorem flatCapDiffeomorph_apply (p : E × ℝ) :
    flatCapDiffeomorph a b ha hb ha0 hb0 p =
      (a p.2 • p.1, b (a p.2 • p.1) * p.2) := rfl

@[simp] theorem flatCapDiffeomorph_symm_apply (p : E × ℝ) :
    (flatCapDiffeomorph a b ha hb ha0 hb0).symm p =
      ((a ((b p.1)⁻¹ * p.2))⁻¹ • p.1, (b p.1)⁻¹ * p.2) := rfl

theorem flatCapDiffeomorph_cap
    (hafar : ∀ z, 1 / 2 ≤ |z| → a z = 1)
    (hbnear : ∀ x, ‖x‖ ≤ 1 / 4 → b x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹)
    (x : E) (hx : ‖x‖ ≤ 1 / 4) (eps : ℝ) (heps : |eps| = 1) :
    flatCapDiffeomorph a b ha hb ha0 hb0
      (x, eps * Real.sqrt (1 - ‖x‖ ^ 2)) = (x, eps) := by
  have hp : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hs := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg (1 - ‖x‖ ^ 2)
  have hfar : 1 / 2 ≤ |eps * Real.sqrt (1 - ‖x‖ ^ 2)| := by
    rw [abs_mul, heps, one_mul, abs_of_nonneg hs0]
    nlinarith [norm_nonneg x]
  rw [flatCapDiffeomorph_apply, hafar _ hfar, one_smul, hbnear x hx]
  congr 1
  rw [mul_left_comm, inv_mul_cancel₀ (Real.sqrt_pos.mpr hp).ne', mul_one]

theorem flatCapDiffeomorph_cylinder
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (q : E) (hq : ‖q‖ = 1) (z : ℝ) (hz : |z| ≤ 1 / 4) :
    flatCapDiffeomorph a b ha hb ha0 hb0
      (Real.sqrt (1 - z ^ 2) • q, z) = (q, z) := by
  have hp : 0 < 1 - z ^ 2 := by
    have hz2 := sq_abs z
    nlinarith [abs_nonneg z]
  rw [flatCapDiffeomorph_apply, hanear z hz, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hp).ne', one_smul,
    hbfar q (by rw [hq]; norm_num), one_mul]

theorem flatCapDiffeomorph_fst_norm_le
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (p : E × ℝ) (hp : ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1) :
    ‖(flatCapDiffeomorph a b ha hb ha0 hb0 p).1‖ ≤ 1 := by
  rw [flatCapDiffeomorph_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hapos p.2)]
  by_cases hz : |p.2| < 1
  · have hr : 0 < 1 - p.2 ^ 2 := by
      nlinarith [sq_abs p.2, abs_nonneg p.2]
    have hsqrt : ‖p.1‖ ≤ Real.sqrt (1 - p.2 ^ 2) :=
      Real.le_sqrt_of_sq_le (by linarith)
    calc
      a p.2 * ‖p.1‖ ≤ (Real.sqrt (1 - p.2 ^ 2))⁻¹ *
          Real.sqrt (1 - p.2 ^ 2) :=
        mul_le_mul (habound p.2 hz) hsqrt (norm_nonneg p.1)
          (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = 1 := inv_mul_cancel₀ (Real.sqrt_pos.mpr hr).ne'
  · have hx : ‖p.1‖ = 0 := by
      have h := le_of_not_gt hz
      nlinarith [sq_abs p.2, norm_nonneg p.1, sq_nonneg ‖p.1‖]
    rw [hx, mul_zero]
    exact zero_le_one

end PoincareConjecture.M25.Topology3D
