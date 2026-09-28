import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledGeometry
import PoincareConjecture.Proofs.M47.TerminalCurvatureRoundLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_scaled_round_carrier_subset_ball
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {epsilon : ℝ} (N : SingularRoundComponent g epsilon) (hsmall : epsilon ≤ 1 / 200)
    {Q H : ℝ} (hQ : 0 < Q) (hH : 0 < H) {x : M} (hx : x ∈ N.carrier)
    (hscalar : H ≤ (rescaledMetric_connection g D Q hQ).scalarCurvature x) :
    N.carrier ⊆ (rescaledMetric g Q hQ).ball x
      (Real.sqrt (144 / H) * Real.sqrt 15 + 1) := by
  rw [rescaledMetric_scalarCurvature] at hscalar
  have hphysical : Q * H ≤ D.scalarCurvature x := by
    have hh := (le_div_iff₀ hQ).mp (show H ≤ D.scalarCurvature x / Q by
      simpa only [div_eq_mul_inv, mul_comm] using hscalar)
    simpa only [mul_comm] using hh
  have hscale : Q * H ≤ 72 * N.scale :=
    hphysical.trans (terminalCurvature_round_scalar_upper D N hsmall hx)
  have hfactor : 0 < Real.sqrt (144 / H) := Real.sqrt_pos.2 (div_pos (by norm_num) hH)
  have hquadratic (y : N.model.carrier) (v : TangentSpace (𝓡 3) y) :
      (rescaledMetric g Q hQ).inner (N.forward y)
        (mfderiv (𝓡 3) (𝓡 3) N.forward y v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward y v) ≤
          Real.sqrt (144 / H) ^ 2 * N.model_metric.inner y v v := by
    have hq := (M44.round_quadratic_bounds N y v).2
    have hmodel : 0 ≤ N.model_metric.inner y v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (N.model_metric.pos y v hv).le
    have hactual : 0 ≤ g.inner (N.forward y) (mfderiv (𝓡 3) (𝓡 3) N.forward y v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward y v) := by
      by_cases hv : mfderiv (𝓡 3) (𝓡 3) N.forward y v = 0
      · simp [hv]
      · exact (g.pos _ _ hv).le
    have hupper : (1 + epsilon) * N.model_metric.inner y v v ≤
        2 * N.model_metric.inner y v v :=
      mul_le_mul_of_nonneg_right (by linarith) hmodel
    have hscaled := mul_le_mul_of_nonneg_right hscale hactual
    have hrewrite : (144 / H) * N.model_metric.inner y v v =
        (144 * N.model_metric.inner y v v) / H := by ring
    rw [rescaledMetric_inner, Real.sq_sqrt (div_nonneg (by norm_num) hH.le), hrewrite]
    apply (le_div_iff₀ hH).mpr
    nlinarith only [hscaled, hq, hupper]
  intro y hy
  have hd := N.model_metric.edist_le_mul_of_inner_mfderiv_le (rescaledMetric g Q hQ)
    (N.forward_smooth.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))) hfactor hquadratic
      (N.inverse x) (N.inverse y)
  rw [N.right_inverse hx, N.right_inverse hy] at hd
  have hb := hd.trans (mul_le_mul_of_nonneg_left
    (terminalCurvature_round_model_distance N (N.inverse x) (N.inverse y)) zero_le)
  rw [← ENNReal.ofReal_mul hfactor.le] at hb
  apply hb.trans_lt
  apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
  linarith

end PoincareConjecture.M47
