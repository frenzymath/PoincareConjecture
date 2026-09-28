import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)
local notation "L2Z" => Lp Z 2 (volume : Measure V)

def fieldIntegral (F : V × Z → ℝ) (u : L2Z) : ℝ := ∫ x, F (x, u x)

theorem integrable_quadratic_field (F : V × Z → ℝ) (hF : Continuous F) {C : ℝ}
    (hb : ∀ x z, ‖F (x, z)‖ ≤ C * ‖z‖ ^ 2) (u : L2Z) :
    Integrable (fun x => F (x, u x)) := by
  apply (((Lp.memLp u).norm.integrable_sq).const_mul C).mono'
  · exact hF.comp_aestronglyMeasurable
      (continuous_id.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable u))
  · exact Eventually.of_forall fun x => hb x (u x)

theorem integral_field_norm_sq (u : L2Z) : (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => (real_inner_self_eq_norm_sq (u x)).symm

theorem fieldIntegral_remainder_le (F : V × Z → ℝ)
    (hi : ∀ u : L2Z, Integrable (fun x => F (x, u x)))
    (u v G : L2Z) {C : ℝ}
    (hR : ∀ᵐ x ∂volume,
      ‖F (x, v x) - F (x, u x) - inner ℝ (G x) (v x - u x)‖ ≤ C * ‖v x - u x‖ ^ 2) :
    ‖fieldIntegral F v - fieldIntegral F u - inner ℝ G (v - u)‖ ≤ C * ‖v - u‖ ^ 2 := by
  have hiG := L2.integrable_inner (𝕜 := ℝ) G (v - u)
  have he : fieldIntegral F v - fieldIntegral F u - inner ℝ G (v - u) =
      ∫ x, F (x, v x) - F (x, u x) - inner ℝ (G x) ((v - u) x) := by
    rw [fieldIntegral, fieldIntegral, L2.inner_def, ← integral_sub (hi v) (hi u)]
    exact (integral_sub ((hi v).sub (hi u)) hiG).symm
  rw [he]
  have hb : ∀ᵐ x ∂volume,
      ‖F (x, v x) - F (x, u x) - inner ℝ (G x) ((v - u) x)‖ ≤ C * ‖(v - u) x‖ ^ 2 := by
    filter_upwards [hR, Lp.coeFn_sub v u] with x hx hsub
    simpa only [hsub, Pi.sub_apply] using hx
  have hbound := norm_integral_le_of_norm_le
    (((Lp.memLp (v - u)).norm.integrable_sq).const_mul C) hb
  simpa only [integral_const_mul, integral_field_norm_sq] using hbound

theorem fieldIntegral_hasFDerivAt (F : V × Z → ℝ)
    (hi : ∀ u : L2Z, Integrable (fun x => F (x, u x)))
    (u G : L2Z) {C : ℝ}
    (hR : ∀ v : L2Z, ∀ᵐ x ∂volume,
      ‖F (x, v x) - F (x, u x) - inner ℝ (G x) (v x - u x)‖ ≤ C * ‖v x - u x‖ ^ 2) :
    HasFDerivAt (fieldIntegral F) (innerSL ℝ G) u := by
  have hb : (fun v : L2Z => fieldIntegral F v - fieldIntegral F u -
      (innerSL ℝ G) (v - u)) =O[𝓝 u] fun v => ‖v - u‖ ^ 2 := by
    apply IsBigO.of_bound C
    apply Eventually.of_forall
    intro v
    simpa only [innerSL_apply_apply, norm_pow, norm_norm] using
      fieldIntegral_remainder_le F hi u v G (hR v)
  rw [hasFDerivAt_iff_isLittleO]
  exact hb.trans_isLittleO (isLittleO_pow_sub_sub u (show 1 < (2 : ℕ) by decide))

end PoincareConjecture.M35.Uniqueness.Heat
