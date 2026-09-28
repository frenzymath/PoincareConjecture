import PoincareConjecture.Proofs.M35.Uniqueness.RotationWeightedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable {g : RiemannianMetric 3 StandardCapSpace}
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation

theorem rotational_metric_split_normSq
    {x n : StandardCapSpace} {r : ℝ} (hr : 0 < r) (hn : ‖n‖ = 1)
    (hx : x = r • n) (v : StandardCapSpace) (d : ℝ) (hv : inner ℝ n v = 0) :
    g.inner x (v + d • n) (v + d • n) =
      axisAngularCoefficient g r * ‖v‖ ^ 2 + axisRadialCoefficient g r * d ^ 2 := by
  have hnorm : ‖x‖ = r := by rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn, mul_one]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hnorm ▸ hr)
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hvn : inner ℝ v n = 0 := by rw [real_inner_comm, hv]
  have hnormv : ‖v + d • n‖ ^ 2 = ‖v‖ ^ 2 + d ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hvn, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, hn]
    ring
  rw [rotational_metric_form g hrotation hx0, hnorm, real_inner_self_eq_norm_sq, hnormv]
  rw [hx, inner_smul_left, inner_add_right, inner_smul_right, hv, hnn]
  simp only [conj_trivial, mul_one, zero_add]
  field_simp
  ring

theorem rotational_connection_skew_radial_split (D : LeviCivitaData g)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hB : ∀ x, inner ℝ x (B x) = 0)
    {x n : StandardCapSpace} {r : ℝ} (hr : 0 < r) (hn : ‖n‖ = 1)
    (hx : x = r • n) (y : StandardCapSpace) (p : ℝ) (hy : inner ℝ n y = 0) :
    D.connection (fun z => B z) x (p • n + y) =
      ((1 + r ^ 2 * radialConnectionAlpha g r) * p) • B n +
        (B y - (inner ℝ n (B y)) • n) +
        ((axisAngularCoefficient g r * (1 + r ^ 2 * radialConnectionAlpha g r) /
          axisRadialCoefficient g r) * inner ℝ n (B y)) • n := by
  have hnorm : ‖x‖ = r := by rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn, mul_one]
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hnorm ▸ hr)
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hswap : inner ℝ y (B n) = -inner ℝ n (B y) := by
    rw [real_inner_comm, ← neg_neg (inner ℝ n (B y)), linear_skew_inner_swap B hB n y]
    ring
  have hbeta : axisAngularCoefficient g r * (1 + r ^ 2 * radialConnectionAlpha g r) /
      axisRadialCoefficient g r = 1 - r ^ 2 * radialConnectionBeta g r := by
    apply (div_eq_iff (axisRadialCoefficient_pos g r).ne').mpr
    simpa only [mul_comm] using (radialConnection_beta_identity g hr).symm
  rw [rotational_connection_linear_skew D hrotation B hB hx0, hnorm, hx, hbeta]
  simp only [map_add, map_smul, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, conj_trivial, hnn, hy, hB n, hswap, mul_one, mul_zero, zero_add,
    add_zero, smul_smul]
  module

end PoincareConjecture.M35.Uniqueness
