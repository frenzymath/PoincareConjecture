import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.RadialFieldSystem
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.IntrinsicWarping

/-!
# Actual intrinsic shape derivatives in retained coordinates

Morgan-Tian Theorem 12.32, pp. 326-327. True arclength differentiates
to one along the actual outward unit field. Thus repeated intrinsic
derivatives of the warping shape are exactly repeated differentiation
along its actual pulled-back field in every retained coordinate chart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

local notation "V" => StandardCapSpace

private theorem norm_hasFDerivAt {x : V} (hx : x ≠ 0) :
    HasFDerivAt (fun y : V => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  convert! h using 1
  ext w
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

/-- Theorem 12.32: actual arclength has unit directional derivative
along the actual outward radial field, without using a model field. -/
theorem radialArclength_norm_radial_derivative
    (g : RiemannianMetric 3 V) {x : V} (hx : x ≠ 0) :
    fderiv ℝ (fun y : V => radialArclength g ‖y‖) x (radialUnitField g x) = 1 := by
  have h := (radialArclength_hasDerivAt g ‖x‖).comp_hasFDerivAt x
    (norm_hasFDerivAt hx)
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp only [smul_apply, innerSL_apply_apply, radialUnitField,
    inner_smul_right, smul_eq_mul, real_inner_self_eq_norm_sq]
  change Real.sqrt (axisRadialCoefficient g ‖x‖) *
    (‖x‖⁻¹ * ((‖x‖ * axisRadialSpeed g ‖x‖)⁻¹ * ‖x‖ ^ 2)) = 1
  unfold axisRadialSpeed
  field_simp [norm_ne_zero_iff.mpr hx,
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g ‖x‖)).ne']

/-- Theorem 12.32: a scalar profile in genuine arclength differentiates
along the actual retained unit field by its ordinary one-dimensional derivative. -/
theorem intrinsic_profile_pullback_directional
    (g : RiemannianMetric 3 V) {f : V → V} {x : V}
    (hf : DifferentiableAt ℝ f x) (hi : (fderiv ℝ f x).IsInvertible)
    (hx : f x ≠ 0) {h : ℝ → ℝ}
    (hh : DifferentiableAt ℝ h (radialArclength g ‖f x‖)) :
    fderiv ℝ (fun y => h (radialArclength g ‖f y‖)) x
      (pullback ℝ f (radialUnitField g) x) = deriv h (radialArclength g ‖f x‖) := by
  let R : V → ℝ := fun y => radialArclength g ‖y‖
  have hR : DifferentiableAt ℝ R (f x) :=
    (radialArclength_hasDerivAt g ‖f x‖).differentiableAt.comp (f x)
      ((norm_hasFDerivAt hx).differentiableAt)
  have hc := (hh.hasDerivAt.comp_hasFDerivAt x (hR.comp x hf).hasFDerivAt).fderiv
  change fderiv ℝ (h ∘ R ∘ f) x (pullback ℝ f (radialUnitField g) x) = _
  rw [hc]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_comp x hR hf, ContinuousLinearMap.comp_apply]
  change deriv h (R (f x)) *
    (fderiv ℝ R (f x) (fderiv ℝ f x ((fderiv ℝ f x).inverse (radialUnitField g (f x))))) = _
  rw [hi.self_apply_inverse, radialArclength_norm_radial_derivative g hx, mul_one]

variable (g : RiemannianMetric 3 V)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : V,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

/-- The actual logarithmic orbit-radius derivative in true arclength. -/
noncomputable def intrinsicRadialShape (s : ℝ) : ℝ :=
  deriv (intrinsicWarpingRadius g hrotation hcomplete) s /
    intrinsicWarpingRadius g hrotation hcomplete s

theorem intrinsicRadialShape_contDiffAt {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ ∞ (intrinsicRadialShape g hrotation hcomplete) s := by
  have hf := intrinsicWarpingRadius_contDiff g hrotation hcomplete
  exact ((contDiff_infty_iff_deriv.mp hf).2.contDiffAt).div hf.contDiffAt
    (intrinsicWarpingRadius_pos g hrotation hcomplete hs).ne'

theorem intrinsicRadialShape_eq {r : ℝ} (hr : 0 < r) :
    intrinsicRadialShape g hrotation hcomplete (radialArclength g r) =
      axisWarpingSlope g r / axisWarpingRadius g r := by
  have hs : 0 < radialArclength g r := by
    simpa only [radialArclength_zero] using (radialArclength_strictMono g) hr
  rw [intrinsicRadialShape,
    (intrinsicWarpingRadius_hasDerivAt g hrotation hcomplete hs).deriv,
    intrinsicWarpingRadius]
  change axisWarpingSlope g
    ((radialArclengthOrderIso g hrotation hcomplete).symm
      ((radialArclengthOrderIso g hrotation hcomplete) r)) /
    axisWarpingRadius g
      ((radialArclengthOrderIso g hrotation hcomplete).symm
        ((radialArclengthOrderIso g hrotation hcomplete) r)) = _
  rw [OrderIso.symm_apply_apply]

private theorem intrinsicRadialShape_iterated_contDiffAt (m : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ ∞ (iteratedDeriv m (intrinsicRadialShape g hrotation hcomplete)) s := by
  induction m with
  | zero =>
    simpa only [iteratedDeriv_zero] using
      intrinsicRadialShape_contDiffAt g hrotation hcomplete hs
  | succ m hm =>
    rw [iteratedDeriv_succ]
    change ContDiffAt ℝ ∞
      (fun y => fderiv ℝ (iteratedDeriv m (intrinsicRadialShape g hrotation hcomplete)) y 1) s
    exact (hm.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- The actual intrinsic shape derivative, pulled through the retained map. -/
noncomputable def intrinsicShapeDerivativePullback (f : V → V) (m : ℕ) (x : V) : ℝ :=
  iteratedDeriv m (intrinsicRadialShape g hrotation hcomplete)
    (radialArclength g ‖f x‖)

theorem intrinsicShapeDerivativePullback_contDiffAt {f : V → V} {x : V}
    (hf : ContDiffAt ℝ ∞ f x) (hx : f x ≠ 0) (m : ℕ) :
    ContDiffAt ℝ ∞ (intrinsicShapeDerivativePullback g hrotation hcomplete f m) x := by
  have hs : 0 < radialArclength g ‖f x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g) (norm_pos_iff.mpr hx)
  exact (intrinsicRadialShape_iterated_contDiffAt g hrotation hcomplete m hs).comp x
    ((radialArclength_contDiff g).contDiffAt.comp x ((contDiffAt_norm ℝ hx).comp x hf))

theorem intrinsicShapeDerivativePullback_zero {f : V → V} {x : V} (hx : f x ≠ 0) :
    intrinsicShapeDerivativePullback g hrotation hcomplete f 0 x =
      axisWarpingSlope g ‖f x‖ / axisWarpingRadius g ‖f x‖ := by
  exact intrinsicRadialShape_eq g hrotation hcomplete (norm_pos_iff.mpr hx)

/-- Theorem 12.32: the successive intrinsic shape derivative is the
actual coordinate directional derivative along the pulled-back unit field. -/
theorem intrinsicShapeDerivativePullback_succ {f : V → V} {x : V}
    (hf : DifferentiableAt ℝ f x) (hi : (fderiv ℝ f x).IsInvertible)
    (hx : f x ≠ 0) (m : ℕ) :
    intrinsicShapeDerivativePullback g hrotation hcomplete f (m + 1) x =
      fderiv ℝ (intrinsicShapeDerivativePullback g hrotation hcomplete f m) x
        (pullback ℝ f (radialUnitField g) x) := by
  have hs : 0 < radialArclength g ‖f x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g) (norm_pos_iff.mpr hx)
  have h := intrinsic_profile_pullback_directional g hf hi hx
    ((intrinsicRadialShape_iterated_contDiffAt g hrotation hcomplete m hs).differentiableAt
      (by simp))
  unfold intrinsicShapeDerivativePullback
  rw [iteratedDeriv_succ]
  exact h.symm

end PoincareMT.M35.Uniqueness
