import PoincareConjecture.Proofs.M47.TerminalCurvatureStaticGeometry









set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

private theorem neck_scale_normalization (N : EpsilonNeck g) :
    N.scale ^ 2 * N.connection.scalarCurvature N.center = 1 := by
  rw [N.scale_eq_scalar, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg N.scalar_center_pos.le, ← Real.sqrt_eq_rpow, inv_pow,
    Real.sq_sqrt N.scalar_center_pos.le, inv_mul_cancel₀ N.scalar_center_pos.ne']



theorem terminalCurvature_neck_scale_window
    (N : EpsilonNeck g) {L H : ℝ} (hL : 0 < L)
    (hlo : L ≤ N.connection.scalarCurvature N.center)
    (hhi : N.connection.scalarCurvature N.center ≤ H) :
    L ≤ N.scale⁻¹ ^ 2 ∧ N.scale⁻¹ ^ 2 ≤ H ∧ N.scale ^ 2 ≤ L⁻¹ := by
  have hnormal := neck_scale_normalization N
  have heq : N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
    apply (mul_left_cancel₀ (sq_pos_of_pos N.scale_pos).ne')
    rw [hnormal, ← mul_pow, mul_inv_cancel₀ N.scale_pos.ne', one_pow]
  refine ⟨heq ▸ hlo, heq ▸ hhi, ?_⟩
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hL).mpr
  calc
    N.scale ^ 2 * L ≤ N.scale ^ 2 * N.connection.scalarCurvature N.center :=
      mul_le_mul_of_nonneg_left hlo (sq_nonneg _)
    _ = 1 := hnormal



theorem terminalCurvature_neck_normalization_error
    (N : EpsilonNeck g) {L sigma R : ℝ} (hsigma : 0 ≤ sigma)
    (hlo : L ≤ N.connection.scalarCurvature N.center)
    (herror : |R - N.connection.scalarCurvature N.center| ≤ sigma * L) :
    |N.scale ^ 2 * R - 1| ≤ sigma := by
  have hnormal := neck_scale_normalization N
  have hfloor : N.scale ^ 2 * L ≤ 1 := by
    calc
      _ ≤ N.scale ^ 2 * N.connection.scalarCurvature N.center :=
        mul_le_mul_of_nonneg_left hlo (sq_nonneg _)
      _ = 1 := hnormal
  calc
    |N.scale ^ 2 * R - 1| = |N.scale ^ 2 * (R - N.connection.scalarCurvature N.center)| := by
      congr 1
      rw [mul_sub, hnormal]
    _ = N.scale ^ 2 * |R - N.connection.scalarCurvature N.center| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ N.scale ^ 2 * (sigma * L) := mul_le_mul_of_nonneg_left herror (sq_nonneg _)
    _ = sigma * (N.scale ^ 2 * L) := by ring
    _ ≤ sigma * 1 := mul_le_mul_of_nonneg_left hfloor hsigma
    _ = sigma := mul_one _

end PoincareConjecture.M47
