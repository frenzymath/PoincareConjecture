import PoincareConjecture.Proofs.M35.RadialGauge.GaugeRestriction
import PoincareConjecture.Proofs.M35.RadialGauge.HeatEquation
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable local instance m35RadialProfileCalculusLocal1 :
    NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35RadialProfileCalculusLocal2 :
    NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem orthogonal_invariant_radial_trace {u : V → ℝ}
    (hu : ∀ (L : V ≃ₗᵢ[ℝ] V) x, u (L x) = u x)
    {e : V} (he : ‖e‖ = 1) :
    u = fun x => u (‖x‖ • e) := by
  funext x
  apply orthogonal_invariant_eq_of_norm_eq hu
  simp only [norm_smul, Real.norm_eq_abs, abs_norm, he, mul_one]

private theorem norm_hasFDerivAt {x : V} (hx : x ≠ 0) :
    HasFDerivAt (fun y : V => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have heq : (fun y : V => Real.sqrt (‖y‖ ^ 2)) = fun y => ‖y‖ :=
    funext (fun y => Real.sqrt_sq (norm_nonneg y))
  rw [heq, Real.sqrt_sq (norm_nonneg x)] at h
  have hcoeff : (1 / (2 * ‖x‖)) • (2 • innerSL ℝ x) = ‖x‖⁻¹ • innerSL ℝ x := by
    ext v
    simp only [two_smul, smul_apply, add_apply, smul_eq_mul]
    field_simp
    ring
  rw [hcoeff] at h
  exact h

theorem radialProfile_hasFDerivAt {w : ℝ → ℝ} {x : V}
    (hw : DifferentiableAt ℝ w ‖x‖) (hx : x ≠ 0) :
    HasFDerivAt (fun y : V => w ‖y‖)
      ((deriv w ‖x‖ / ‖x‖) • innerSL ℝ x) x := by
  simpa only [smul_smul, div_eq_mul_inv, Function.comp_def] using
    hw.hasDerivAt.comp_hasFDerivAt x (norm_hasFDerivAt hx)

theorem radialProfile_fderiv_norm {w : ℝ → ℝ} {x : V}
    (hw : DifferentiableAt ℝ w ‖x‖) (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : V => w ‖y‖) x‖ = |deriv w ‖x‖| := by
  rw [(radialProfile_hasFDerivAt hw hx).fderiv, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs, abs_div, abs_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem radialProfile_hessian_apply {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    {x : V} (hx : x ≠ 0) (a b : V) :
    fderiv ℝ (fderiv ℝ (fun y : V => w ‖y‖)) x a b =
      deriv w ‖x‖ / ‖x‖ * ⟪a, b⟫ +
      (deriv (deriv w) ‖x‖ * ‖x‖ - deriv w ‖x‖) / ‖x‖ ^ 3 *
        ⟪x, a⟫ * ⟪x, b⟫ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hw' := (contDiff_infty_iff_deriv.mp hw).2
  have hq := (((hw'.differentiable (by simp) ‖x‖).hasDerivAt).div
    (hasDerivAt_id ‖x‖) hn).comp_hasFDerivAt x (norm_hasFDerivAt hx)
  have hH := hq.smul ((innerSL ℝ (E := V)).hasFDerivAt (x := x))
  have heq : fderiv ℝ (fun y : V => w ‖y‖) =ᶠ[𝓝 x]
      fun y => (deriv w ‖y‖ / ‖y‖) • innerSL ℝ y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact (radialProfile_hasFDerivAt (hw.differentiable (by simp) ‖y‖) hy).fderiv
  have hactual := hH.congr_of_eventuallyEq heq
  rw [hactual.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul, Function.comp_def, Pi.div_apply, id_eq, mul_one]
  change deriv w ‖x‖ / ‖x‖ * ⟪a, b⟫ +
    ((deriv (deriv w) ‖x‖ * ‖x‖ - deriv w ‖x‖) / ‖x‖ ^ 2) *
      (‖x‖⁻¹ * ⟪x, a⟫) * ⟪x, b⟫ = _
  field_simp

theorem radialProfile_euclideanLaplacian {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    {x : V} (hx : x ≠ 0) :
    euclideanLaplacian (fun y : V => w ‖y‖) x =
      deriv (deriv w) ‖x‖ + (n : ℝ) * deriv w ‖x‖ / ‖x‖ := by
  let e := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hsum : (∑ i : Fin (n + 1), ⟪x, e i⟫ * ⟪x, e i⟫) = ‖x‖ ^ 2 := by
    simpa only [pow_two] using e.sum_sq_inner_left x
  have he (i : Fin (n + 1)) : ⟪e i, e i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, e.norm_eq_one, one_pow]
  rw [euclideanLaplacian]
  simp only [← EuclideanSpace.basisFun_apply]
  change (∑ i : Fin (n + 1),
    fderiv ℝ (fderiv ℝ (fun y : V => w ‖y‖)) x (e i) (e i)) = _
  simp_rw [radialProfile_hessian_apply hw hx, he]
  simp only [mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hsum]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

end PoincareConjecture.M35.RadialGauge
