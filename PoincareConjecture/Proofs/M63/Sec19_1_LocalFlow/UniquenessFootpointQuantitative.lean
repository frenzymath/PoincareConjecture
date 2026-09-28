import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessLocalFootpoint
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set
open scoped ContDiff RealInnerProductSpace

namespace PoincareConjecture.M63

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem curveFootpointResidual_partial_at {r : ℝ → E} (hr : ContDiff ℝ ∞ r)
    (z : E) (y : ℝ) :
    (fderiv ℝ (curveFootpointResidual r) (z, y)).comp
        (ContinuousLinearMap.inr ℝ E ℝ) =
      (-‖deriv r y‖ ^ 2 + ⟪z - r y, deriv (deriv r) y⟫) •
        ContinuousLinearMap.id ℝ ℝ := by
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).1
  have hr₂ := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hr).2).1
  have hpartial : HasDerivAt (fun s => curveFootpointResidual r (z, s))
      (-‖deriv r y‖ ^ 2 + ⟪z - r y, deriv (deriv r) y⟫) y := by
    simpa only [curveFootpointResidual, Pi.sub_apply, zero_sub, inner_neg_left,
      real_inner_self_eq_norm_sq, add_comm] using
      (((hasDerivAt_const y z).sub (hr₁ y).hasDerivAt).inner ℝ
        (hr₂ y).hasDerivAt)
  have hprod : (0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.inr ℝ E ℝ := by
    apply ContinuousLinearMap.ext
    intro s
    rfl
  have hslice : HasFDerivAt (fun s => curveFootpointResidual r (z, s))
      ((fderiv ℝ (curveFootpointResidual r) (z, y)).comp
        (ContinuousLinearMap.inr ℝ E ℝ)) y := by
    simpa only [Function.comp_def, hprod] using
      ((curveFootpointResidual_contDiff hr).differentiable (by simp)
        (z, y)).hasFDerivAt.comp y
          ((hasFDerivAt_const z y).prodMk (hasFDerivAt_id y))
  rw [hslice.unique hpartial.hasFDerivAt]
  apply ContinuousLinearMap.ext
  intro s
  change s * _ = _ * s
  exact mul_comm _ _




theorem curveFootpoint_denominator_lower {r : ℝ → E} (hr : ContDiff ℝ ∞ r)
    {m M B rho eps x y : ℝ} {z : E}
    (hm : 0 < m) (hM : 0 < M) (_hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hz : ‖z - r x‖ < eps) (hy : y ∈ Icc (x - rho) (x + rho)) :
    m ^ 2 / 2 ≤ ‖deriv r y‖ ^ 2 - ⟪z - r y, deriv (deriv r) y⟫ := by
  have hxy : |y - x| ≤ rho := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hLip : ‖r y - r x‖ ≤ M * |y - x| := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun s _ => (hr.differentiable (by simp) s)) (fun s _ => hupper s)
        (mem_univ x) (mem_univ y)
  have hdist : ‖z - r y‖ ≤ eps + M * rho := calc
    ‖z - r y‖ ≤ ‖z - r x‖ + ‖r x - r y‖ := by
      simpa only [dist_eq_norm] using dist_triangle z (r x) (r y)
    _ = ‖z - r x‖ + ‖r y - r x‖ := by rw [norm_sub_rev (r x) (r y)]
    _ ≤ eps + M * rho := add_le_add hz.le (hLip.trans (mul_le_mul_of_nonneg_left hxy hM.le))
  have hinner : ⟪z - r y, deriv (deriv r) y⟫ ≤ (eps + M * rho) * B :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul hdist (hsecond y) (norm_nonneg _) (by positivity))
  have hsquare : m ^ 2 ≤ ‖deriv r y‖ ^ 2 := by
    nlinarith [hlower y, norm_nonneg (deriv r y)]
  nlinarith




theorem existsUnique_curveFootpoint_near {r : ℝ → E} (hr : ContDiff ℝ ∞ r)
    {m M B rho eps x : ℝ} {z : E}
    (hm : 0 < m) (hM : 0 < M) (hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hmargin : 4 * eps * M ≤ m ^ 2 * rho) (hz : ‖z - r x‖ < eps) :
    ∃! y, |y - x| < rho ∧ curveFootpointResidual r (z, y) = 0 := by
  let H : ℝ → ℝ := fun s => curveFootpointResidual r (z, s)
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).1
  have hr₂ := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hr).2).1
  have hderiv (s : ℝ) : HasDerivAt H
      (-‖deriv r s‖ ^ 2 + ⟪z - r s, deriv (deriv r) s⟫) s := by
    simpa only [H, curveFootpointResidual, Pi.sub_apply, zero_sub, inner_neg_left,
      real_inner_self_eq_norm_sq, add_comm] using
      (((hasDerivAt_const s z).sub (hr₁ s).hasDerivAt).inner ℝ
        (hr₂ s).hasDerivAt)
  have hcontinuous : Continuous H := continuous_iff_continuousAt.mpr
    (fun s => (hderiv s).continuousAt)
  have hdifferentiable : Differentiable ℝ H := fun s => (hderiv s).differentiableAt
  have hbound (s : ℝ) (hs : s ∈ Icc (x - rho) (x + rho)) : deriv H s ≤ -(m ^ 2 / 2) := by
    rw [(hderiv s).deriv]
    have h := curveFootpoint_denominator_lower hr hm hM hB hrho heps
      hlower hupper hsecond hsmall hz hs
    linarith
  have hx : x ∈ Icc (x - rho) (x + rho) := ⟨by linarith, by linarith⟩
  have hab : x - rho ≤ x + rho := by linarith
  have hleft := (convex_Icc (x - rho) (x + rho)).image_sub_le_mul_sub_of_deriv_le
    hcontinuous.continuousOn hdifferentiable.differentiableOn
    (fun s hs => hbound s (interior_subset hs))
    (x - rho) (left_mem_Icc.mpr hab) x hx (by linarith)
  have hright := (convex_Icc (x - rho) (x + rho)).image_sub_le_mul_sub_of_deriv_le
    hcontinuous.continuousOn hdifferentiable.differentiableOn
    (fun s hs => hbound s (interior_subset hs))
    x hx (x + rho) (right_mem_Icc.mpr hab) (by linarith)
  have hcenter : |H x| ≤ eps * M :=
    (abs_real_inner_le_norm (z - r x) (deriv r x)).trans
      (mul_le_mul hz.le (hupper x) (norm_nonneg _) heps.le)
  have hpositive : 0 < m ^ 2 * rho := mul_pos (sq_pos_of_pos hm) hrho
  have hleftpos : 0 < H (x - rho) := by
    have hcenterlo := (abs_le.mp hcenter).1
    nlinarith
  have hrightneg : H (x + rho) < 0 := by
    have hcenterhi := (abs_le.mp hcenter).2
    nlinarith
  obtain ⟨y, hy, hzero⟩ := intermediate_value_Ioo' hab hcontinuous.continuousOn
    (show (0 : ℝ) ∈ Ioo (H (x + rho)) (H (x - rho)) from ⟨hrightneg, hleftpos⟩)
  have hstrict : StrictAntiOn H (Icc (x - rho) (x + rho)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hcontinuous.continuousOn
      (fun s hs => (hbound s (interior_subset hs)).trans_lt (by nlinarith [sq_pos_of_pos hm]))
  refine ⟨y, ⟨abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩, hzero⟩, ?_⟩
  intro y' hy'
  have hy'window : y' ∈ Icc (x - rho) (x + rho) := by
    have habs := abs_lt.mp hy'.1
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  exact hstrict.injOn hy'window (Ioo_subset_Icc_self hy) (hy'.2.trans hzero.symm)

end PoincareConjecture.M63
