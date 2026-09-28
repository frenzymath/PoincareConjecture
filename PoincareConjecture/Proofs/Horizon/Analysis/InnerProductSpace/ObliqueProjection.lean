import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

set_option autoImplicit false

open scoped InnerProductSpace

namespace Poincare.InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem inner_sub_normal_component (x v : E) :
    ⟪x, v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x⟫_ℝ = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem norm_sub_normal_component_le (x v : E) :
    ‖v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x‖ ≤ ‖v‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have heq : ‖v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x‖ ^ 2 =
      ‖v‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm v x, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    ring
  have hnonneg : 0 ≤ ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := div_nonneg (sq_nonneg _) hn.le
  nlinarith [norm_nonneg (v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x), norm_nonneg v]

theorem norm_sub_functional_component_le (ell : F →L[ℝ] ℝ) (u v : F) :
    ‖v - (ell v / ell u) • u‖ ≤
      (1 + ‖ell‖ * ‖u‖ / |ell u|) * ‖v‖ := by
  have hv : |ell v| ≤ ‖ell‖ * ‖v‖ := by simpa only [Real.norm_eq_abs] using ell.le_opNorm v
  calc
    ‖v - (ell v / ell u) • u‖ ≤ ‖v‖ + ‖(ell v / ell u) • u‖ := norm_sub_le _ _
    _ = ‖v‖ + |ell v| / |ell u| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_div]
    _ ≤ ‖v‖ + (‖ell‖ * ‖v‖) / |ell u| * ‖u‖ := by
      gcongr
    _ = (1 + ‖ell‖ * ‖u‖ / |ell u|) * ‖v‖ := by ring

theorem norm_project_after_linearMap_le (L : E →L[ℝ] F)
    (ell : F →L[ℝ] ℝ) (x : E) (u : F) {a A : ℝ}
    (hLu : L x = a • u) (hell : ell u ≠ 0) (hA : 0 ≤ A)
    (hL : ∀ w, ⟪x, w⟫_ℝ = 0 → ‖L w‖ ≤ A * ‖w‖) (v : E) :
    ‖L v - (ell (L v) / ell u) • u‖ ≤
      (1 + ‖ell‖ * ‖u‖ / |ell u|) * A * ‖v‖ := by
  let w := v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x
  have hw : ⟪x, w⟫_ℝ = 0 := inner_sub_normal_component x v
  have hn : ‖w‖ ≤ ‖v‖ := norm_sub_normal_component_le x v
  have heq : L v - (ell (L v) / ell u) • u = L w - (ell (L w) / ell u) • u := by
    dsimp only [w]
    simp only [map_sub, map_smul, hLu, smul_smul, smul_eq_mul]
    have halg : (ell (L v) - (⟪x, v⟫_ℝ / ‖x‖ ^ 2 * a) * ell u) / ell u =
        ell (L v) / ell u - (⟪x, v⟫_ℝ / ‖x‖ ^ 2 * a) := by field_simp
    rw [halg]
    module
  rw [heq]
  have hfactor : 0 ≤ 1 + ‖ell‖ * ‖u‖ / |ell u| := by positivity
  calc
    ‖L w - (ell (L w) / ell u) • u‖ ≤
        (1 + ‖ell‖ * ‖u‖ / |ell u|) * ‖L w‖ :=
      norm_sub_functional_component_le ell u (L w)
    _ ≤ (1 + ‖ell‖ * ‖u‖ / |ell u|) * (A * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((hL w hw).trans (mul_le_mul_of_nonneg_left hn hA)) hfactor
    _ = _ := by ring

theorem norm_project_after_linearMap_le_of_angle (L : E →L[ℝ] F)
    (x : E) (u vnormal : F) {a A c : ℝ}
    (hLu : L x = a • u) (hc : 0 < c) (hpair : ⟪vnormal, u⟫_ℝ ≤ -c)
    (hu : ‖u‖ ≤ 1) (hv : ‖vnormal‖ ≤ 1) (hA : 0 ≤ A)
    (hL : ∀ w, ⟪x, w⟫_ℝ = 0 → ‖L w‖ ≤ A * ‖w‖) (w : E) :
    ‖L w - (⟪vnormal, L w⟫_ℝ / ⟪vnormal, u⟫_ℝ) • u‖ ≤
      (1 + 1 / c) * A * ‖w‖ := by
  let ell : F →L[ℝ] ℝ := innerSL ℝ vnormal
  have hell : ell u ≠ 0 := by change ⟪vnormal, u⟫_ℝ ≠ 0; linarith
  have helnorm : ‖ell‖ ≤ 1 := by
    apply ell.opNorm_le_bound zero_le_one
    intro z
    exact (norm_inner_le_norm vnormal z).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  have hcabs : c ≤ |ell u| := by
    change c ≤ |⟪vnormal, u⟫_ℝ|
    exact (by linarith : c ≤ -⟪vnormal, u⟫_ℝ).trans (neg_le_abs _)
  have hprod : ‖ell‖ * ‖u‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul helnorm hu (norm_nonneg u) zero_le_one
  have hcoef : ‖ell‖ * ‖u‖ / |ell u| ≤ 1 / c :=
    (div_le_div_of_nonneg_right hprod (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left zero_le_one hc hcabs)
  exact (norm_project_after_linearMap_le L ell x u hLu hell hA hL w).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hcoef) hA) (norm_nonneg _))

theorem inner_le_neg_eighth_of_small_sum (u v : F) {δ : ℝ}
    (hu : 1 / 2 ≤ ‖u‖) (hv : 1 / 2 ≤ ‖v‖)
    (hsum : ‖u + v‖ ^ 2 ≤ 4 * δ) (hδ : δ ≤ 1 / 16) :
    ⟪u, v⟫_ℝ ≤ -(1 / 8) := by
  rw [norm_add_sq_real] at hsum
  nlinarith [norm_nonneg u, norm_nonneg v]

end Poincare.InnerProductSpace
