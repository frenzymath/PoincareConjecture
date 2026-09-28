import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt









set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {S X Y : Type*} [TopologicalSpace S]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

set_option backward.isDefEq.respectTransparency false in

theorem eventually_sqrt_bilinear_comparison
    {B : S → X →L[ℝ] X →L[ℝ] ℝ} {s₀ : S} (hB : ContinuousAt B s₀)
    (L : X ≃L[ℝ] Y) (hcenter : ∀ v : X, B s₀ v v = ‖L v‖ ^ 2)
    {r : ℝ} (hr : 1 < r) :
    ∀ᶠ s in 𝓝 s₀, ∀ v : X,
      ‖L v‖ / r ≤ Real.sqrt (B s v v) ∧ Real.sqrt (B s v v) ≤ r * ‖L v‖ := by
  let A : ℝ := 1 + ‖L.symm.toContinuousLinearMap‖
  have hA : 0 < A := by dsimp only [A]; positivity
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hri : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hri1 : r⁻¹ < 1 := (inv_lt_one₀ hrpos).mpr hr
  have hd₁ : 0 < r ^ 2 - 1 := by nlinarith
  have hd₂ : 0 < 1 - (r⁻¹) ^ 2 := by
    have hs := (sq_lt_sq₀ hri.le zero_le_one).mpr hri1
    nlinarith
  let d : ℝ := min (r ^ 2 - 1) (1 - (r⁻¹) ^ 2)
  have hd : 0 < d := lt_min hd₁ hd₂
  have heps : 0 < d / A ^ 2 := div_pos hd (sq_pos_of_pos hA)
  have hnear : ∀ᶠ s in 𝓝 s₀, ‖B s - B s₀‖ < d / A ^ 2 := by
    have hb := hB (Metric.ball_mem_nhds (B s₀) heps)
    change ∀ᶠ s in 𝓝 s₀, dist (B s) (B s₀) < d / A ^ 2 at hb
    filter_upwards [hb] with s hs
    rwa [dist_eq_norm (B s) (B s₀)] at hs
  filter_upwards [hnear] with s hs
  intro v
  have hv : ‖v‖ ≤ A * ‖L v‖ := calc
    ‖v‖ = ‖L.symm (L v)‖ := by rw [L.symm_apply_apply]
    _ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L v‖ :=
      L.symm.toContinuousLinearMap.le_opNorm (L v)
    _ ≤ A * ‖L v‖ := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)
  have herror : |B s v v - ‖L v‖ ^ 2| ≤ d * ‖L v‖ ^ 2 := calc
    _ = ‖(B s - B s₀) v v‖ := by
      change |B s v v - ‖L v‖ ^ 2| = |B s v v - B s₀ v v|
      rw [hcenter]
    _ ≤ ‖B s - B s₀‖ * ‖v‖ * ‖v‖ := (B s - B s₀).le_opNorm₂ v v
    _ ≤ (d / A ^ 2) * (A * ‖L v‖) * (A * ‖L v‖) := by gcongr
    _ = (d / A ^ 2 * A ^ 2) * ‖L v‖ ^ 2 := by ring
    _ = d * ‖L v‖ ^ 2 := by rw [div_mul_cancel₀ d (sq_pos_of_pos hA).ne']
  have hupper : B s v v ≤ (r * ‖L v‖) ^ 2 := by
    have hdu := mul_le_mul_of_nonneg_right (min_le_left (r ^ 2 - 1)
      (1 - (r⁻¹) ^ 2)) (sq_nonneg ‖L v‖)
    have he := (abs_le.mp herror).2
    dsimp only [d] at he
    nlinarith
  have hlower : (‖L v‖ / r) ^ 2 ≤ B s v v := by
    have hdl := mul_le_mul_of_nonneg_right (min_le_right (r ^ 2 - 1)
      (1 - (r⁻¹) ^ 2)) (sq_nonneg ‖L v‖)
    have he := (abs_le.mp herror).1
    dsimp only [d] at he
    rw [div_eq_mul_inv]
    nlinarith
  have hnonneg : 0 ≤ B s v v := (sq_nonneg _).trans hlower
  refine ⟨?_, (Real.sqrt_le_iff).mpr ⟨mul_nonneg hrpos.le (norm_nonneg _), hupper⟩⟩
  have hsqrt := Real.sq_sqrt hnonneg
  have hdiv : 0 ≤ ‖L v‖ / r := div_nonneg (norm_nonneg _) hrpos.le
  nlinarith [Real.sqrt_nonneg (B s v v)]

end PoincareConjecture.M10
