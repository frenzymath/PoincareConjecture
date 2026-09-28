import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialCoordinate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

noncomputable def intrinsicInverseScale (s : ℝ) : ℝ :=
  axisDivision (radialArclengthOrderIso g hrotation hcomplete).symm s

theorem intrinsicInverseScale_contDiff :
    ContDiff ℝ ∞ (intrinsicInverseScale g hrotation hcomplete) :=
  axisDivision_contDiff (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)

theorem intrinsicInverseScale_even :
    Function.Even (intrinsicInverseScale g hrotation hcomplete) :=
  axisDivision_even_of_odd (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)
    (radialArclengthOrderIso_symm_odd g hrotation hcomplete)

theorem mul_intrinsicInverseScale (s : ℝ) :
    s * intrinsicInverseScale g hrotation hcomplete s =
      (radialArclengthOrderIso g hrotation hcomplete).symm s := by
  rw [intrinsicInverseScale,
    mul_axisDivision (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete),
    radialArclengthOrderIso_symm_zero, sub_zero]

theorem intrinsicInverseScale_zero : intrinsicInverseScale g hrotation hcomplete 0 =
    (Real.sqrt (axisRadialCoefficient g 0))⁻¹ := by
  rw [intrinsicInverseScale, axisDivision_zero,
    (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete 0).deriv,
    radialArclengthOrderIso_symm_zero]

theorem intrinsicInverseScale_pos {s : ℝ} (hs : 0 < s) :
    0 < intrinsicInverseScale g hrotation hcomplete s := by
  have h := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  rw [← mul_intrinsicInverseScale g hrotation hcomplete] at h
  exact (mul_pos_iff_of_pos_left hs).mp h

theorem intrinsicInverseScale_radial_derivative (s : ℝ) :
    intrinsicInverseScale g hrotation hcomplete s + s ^ 2 *
      axisDivision (deriv (intrinsicInverseScale g hrotation hcomplete)) s =
    (Real.sqrt (axisRadialCoefficient g
      ((radialArclengthOrderIso g hrotation hcomplete).symm s)))⁻¹ := by
  let k := intrinsicInverseScale g hrotation hcomplete
  have hk : ContDiff ℝ ∞ k := intrinsicInverseScale_contDiff g hrotation hcomplete
  have he : Function.Even k := intrinsicInverseScale_even g hrotation hcomplete
  have heq : (fun r => r * k r) =
      ((radialArclengthOrderIso g hrotation hcomplete).symm : ℝ → ℝ) :=
    funext (mul_intrinsicInverseScale g hrotation hcomplete)
  have hd : HasDerivAt (fun r => r * k r) (k s + s * deriv k s) s := by
    have hh := (hasDerivAt_id s).mul (hk.differentiable (by simp) s).hasDerivAt
    change HasDerivAt (fun r => r * k r) (1 * k s + s * deriv k s) s at hh
    simpa only [one_mul] using hh
  rw [heq] at hd
  have hu := hd.unique (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete s)
  have hs := mul_axisDivision_deriv hk he s
  change k s + s ^ 2 * axisDivision (deriv k) s = _
  calc
    _ = k s + s * deriv k s := by rw [← hs]; ring
    _ = _ := hu

theorem intrinsicSpatialInverse_fderiv (x v : StandardCapSpace) :
    fderiv ℝ (intrinsicSpatialInverse g hrotation hcomplete) x v =
      intrinsicInverseScale g hrotation hcomplete ‖x‖ • v +
        (axisDivision (deriv (intrinsicInverseScale g hrotation hcomplete)) ‖x‖ *
          inner ℝ x v) • x := by
  let k := intrinsicInverseScale g hrotation hcomplete
  have hd := (hasFDerivAt_even_norm
    (intrinsicInverseScale_contDiff g hrotation hcomplete)
    (intrinsicInverseScale_even g hrotation hcomplete) x).smul (hasFDerivAt_id x)
  change HasFDerivAt (fun y => k ‖y‖ • y) _ x at hd
  change fderiv ℝ (fun y => k ‖y‖ • y) x v = _
  rw [hd.fderiv]
  rfl

theorem intrinsicSpatialInverse_fderiv_zero (v : StandardCapSpace) :
    fderiv ℝ (intrinsicSpatialInverse g hrotation hcomplete) 0 v =
      (Real.sqrt (axisRadialCoefficient g 0))⁻¹ • v := by
  rw [intrinsicSpatialInverse_fderiv, norm_zero, intrinsicInverseScale_zero]
  simp only [inner_zero_left, mul_zero, zero_smul, add_zero]

end PoincareConjecture.M35.Uniqueness
