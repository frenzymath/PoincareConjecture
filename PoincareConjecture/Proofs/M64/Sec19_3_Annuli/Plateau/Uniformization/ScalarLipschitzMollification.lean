import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.Mollifier
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

set_option autoImplicit false

noncomputable section

open MeasureTheory ContinuousLinearMap Set Filter
open scoped Convolution ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem scalarVector_normed_convolution_lipschitz {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) (phi : ContDiffBump (0 : Plane)) :
    LipschitzWith L (phi.normed volume ⋆[lsmul ℝ ℝ, volume] u) := by
  have hi : ConvolutionExists (phi.normed volume) u (lsmul ℝ ℝ) volume :=
    phi.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) phi.continuous_normed.locallyIntegrable hu.continuous
  have hint (x : Plane) : Integrable (fun t => phi.normed volume t • u (x - t)) volume :=
    (hi x).integrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, convolution_def, lsmul_apply]
  rw [← integral_sub (hint x) (hint y)]
  calc
    _ ≤ ∫ t, ‖phi.normed volume t • u (x - t) - phi.normed volume t • u (y - t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, phi.normed volume t * ((L : ℝ) * ‖x - y‖) := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · exact phi.integrable_normed.mul_const _
      · apply Eventually.of_forall
        intro t
        dsimp only
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t)]
        apply mul_le_mul_of_nonneg_left _ (phi.nonneg_normed t)
        simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
          hu.dist_le_mul (x - t) (y - t)
    _ = (L : ℝ) * ‖x - y‖ := by
      rw [integral_mul_const, phi.integral_normed, one_mul]

theorem scalarVector_mollifier_error {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) {r : ℝ} (hr : 0 < r) (x : Plane) :
    dist ((mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) x) (u x) ≤ (L : ℝ) * r := by
  apply dist_convolution_le (mul_nonneg L.coe_nonneg hr.le)
    (by rw [mollifierEps_support_eq]) (mollifierEps_nonneg hr)
    (mollifierEps_integral_eq_one hr) hu.continuous.aestronglyMeasurable
  intro y hy
  exact (hu.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le L.coe_nonneg)

omit [CompleteSpace E] in

theorem scalarVector_mollifier_smooth {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) :=
  (mollifierEps_compactSupport hr).contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifierEps_smooth hr) hu.continuous.locallyIntegrable

omit [CompleteSpace E] in

theorem scalarVector_mollifier_derivative_bound {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) {r : ℝ} (hr : 0 < r) (x : Plane) :
    ‖fderiv ℝ (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) x‖ ≤ (L : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ
    (scalarVector_normed_convolution_lipschitz hu (mollifierBumpEps hr))

theorem scalarVector_mollifier_uniform {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hz : Tendsto r atTop (𝓝 0)) :
    TendstoUniformly (fun j => mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u) u atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro eps heps
  have hbound : Tendsto (fun j => (L : ℝ) * r j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hz.const_mul (L : ℝ)
  filter_upwards [hbound.eventually (gt_mem_nhds heps)] with j hj x
  exact (dist_comm _ _).trans_lt ((scalarVector_mollifier_error hu (hr j) x).trans_lt hj)

end PoincareConjecture.M64Uniformization
