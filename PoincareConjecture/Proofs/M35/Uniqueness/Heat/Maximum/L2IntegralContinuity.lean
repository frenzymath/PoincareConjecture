import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.L2IntegralVariation
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.LpNormBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)
local notation "L2Z" => Lp Z 2 (volume : Measure V)

theorem integrable_pointNorm_mul (u v : L2Z) :
    Integrable (fun x => ‖u x‖ * ‖v x‖) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (lpPointNorm u) (lpPointNorm v)).congr
  filter_upwards [lpPointNorm_coe u, lpPointNorm_coe v] with x hu hv
  simp only [hu, hv, RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem integral_pointNorm_mul_le (u v : L2Z) :
    (∫ x, ‖u x‖ * ‖v x‖) ≤ ‖u‖ * ‖v‖ := by
  have he : (∫ x, ‖u x‖ * ‖v x‖) = inner ℝ (lpPointNorm u) (lpPointNorm v) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpPointNorm_coe u, lpPointNorm_coe v] with x hu hv
    simp only [hu, hv, RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  rw [he]
  simpa only [norm_lpPointNorm] using real_inner_le_norm (lpPointNorm u) (lpPointNorm v)

theorem fieldIntegral_difference_le (F : V × Z → ℝ)
    (hi : ∀ u : L2Z, Integrable (fun x => F (x, u x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x z w, ‖F (x, z) - F (x, w)‖ ≤ C * (‖z‖ + ‖w‖) * ‖z - w‖)
    (u v : L2Z) :
    ‖fieldIntegral F v - fieldIntegral F u‖ ≤ C * (‖v‖ + ‖u‖) * ‖v - u‖ := by
  have he : fieldIntegral F v - fieldIntegral F u = ∫ x, F (x, v x) - F (x, u x) :=
    (integral_sub (hi v) (hi u)).symm
  have hiB : Integrable (fun x => C *
      (‖v x‖ * ‖(v - u) x‖ + ‖u x‖ * ‖(v - u) x‖)) :=
    ((integrable_pointNorm_mul v (v - u)).add
      (integrable_pointNorm_mul u (v - u))).const_mul C
  have hbound : ∀ᵐ x ∂volume, ‖F (x, v x) - F (x, u x)‖ ≤ C *
      (‖v x‖ * ‖(v - u) x‖ + ‖u x‖ * ‖(v - u) x‖) := by
    filter_upwards [Lp.coeFn_sub v u] with x hx
    simp only [hx, Pi.sub_apply]
    convert! hb x (v x) (u x) using 1
    ring
  rw [he]
  apply (norm_integral_le_of_norm_le hiB hbound).trans
  rw [integral_const_mul,
    integral_add (integrable_pointNorm_mul v (v - u)) (integrable_pointNorm_mul u (v - u))]
  calc
    _ ≤ C * (‖v‖ * ‖v - u‖ + ‖u‖ * ‖v - u‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (integral_pointNorm_mul_le v (v - u))
        (integral_pointNorm_mul_le u (v - u))) hC
    _ = _ := by ring

theorem fieldIntegral_continuous (F : V × Z → ℝ)
    (hi : ∀ u : L2Z, Integrable (fun x => F (x, u x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x z w, ‖F (x, z) - F (x, w)‖ ≤ C * (‖z‖ + ‖w‖) * ‖z - w‖) :
    Continuous (fieldIntegral F) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm (fun v => fieldIntegral_difference_le F hi hC hb u v)
  have hc : Continuous (fun v : L2Z => C * (‖v‖ + ‖u‖) * ‖v - u‖) := by fun_prop
  simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto u

end PoincareConjecture.M35.Uniqueness.Heat
