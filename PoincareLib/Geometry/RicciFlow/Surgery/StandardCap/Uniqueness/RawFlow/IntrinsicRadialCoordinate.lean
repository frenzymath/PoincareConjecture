import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.RadialArclength
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The actual smooth intrinsic radial coordinate

Morgan-Tian Section 12.6, pp. 307-309. Rotational symmetry makes the
axis coefficients even. The genuine arclength integral is therefore odd,
and completeness and its positive derivative make it a smooth global
coordinate with a smooth inverse, including at zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix

namespace PoincareMT.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

private noncomputable def radialHalfTurn : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

private theorem radialHalfTurn_axis (r : ℝ) :
    standardRotation radialHalfTurn (r • e 2) = (-r) • e 2 := by
  ext i
  fin_cases i <;> simp [standardRotation, radialHalfTurn, e, EuclideanSpace.single, dotProduct]

private theorem radialHalfTurn_radial : standardRotation radialHalfTurn (e 2) = -e 2 := by
  simpa only [one_smul, neg_one_smul] using radialHalfTurn_axis 1

private theorem radialHalfTurn_angular : standardRotation radialHalfTurn (e 0) = e 0 := by
  ext i
  fin_cases i <;> simp [standardRotation, radialHalfTurn, e, EuclideanSpace.single, dotProduct]

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation

/-- Section 12.6: the actual radial axis coefficient is even through the tip. -/
theorem axisRadialCoefficient_even : Function.Even (axisRadialCoefficient g) := by
  intro r
  change g.euclideanCoefficients ((-r) • e 2) (e 2) (e 2) =
    g.euclideanCoefficients (r • e 2) (e 2) (e 2)
  have h := hrotation radialHalfTurn (r • e 2) (e 2) (e 2)
  rw [standardRotation_mfderiv] at h
  change g.inner (standardRotation radialHalfTurn (r • e 2))
    (standardRotation radialHalfTurn (e 2)) (standardRotation radialHalfTurn (e 2)) = _ at h
  change g.euclideanCoefficients (standardRotation radialHalfTurn (r • e 2))
    (standardRotation radialHalfTurn (e 2)) (standardRotation radialHalfTurn (e 2)) =
      g.euclideanCoefficients (r • e 2) (e 2) (e 2) at h
  simpa only [radialHalfTurn_axis, radialHalfTurn_radial, map_neg, neg_apply, neg_neg] using h

/-- Section 12.6: the actual angular axis coefficient is even through the tip. -/
theorem axisAngularCoefficient_even : Function.Even (axisAngularCoefficient g) := by
  intro r
  change g.euclideanCoefficients ((-r) • e 2) (e 0) (e 0) =
    g.euclideanCoefficients (r • e 2) (e 0) (e 0)
  have h := hrotation radialHalfTurn (r • e 2) (e 0) (e 0)
  rw [standardRotation_mfderiv] at h
  change g.inner (standardRotation radialHalfTurn (r • e 2))
    (standardRotation radialHalfTurn (e 0)) (standardRotation radialHalfTurn (e 0)) = _ at h
  change g.euclideanCoefficients (standardRotation radialHalfTurn (r • e 2))
    (standardRotation radialHalfTurn (e 0)) (standardRotation radialHalfTurn (e 0)) =
      g.euclideanCoefficients (r • e 2) (e 0) (e 0) at h
  simpa only [radialHalfTurn_axis, radialHalfTurn_angular] using h

omit hrotation in
/-- Section 12.6: the actual radial arclength is smooth on the full axis. -/
theorem radialArclength_contDiff : ContDiff ℝ ∞ (radialArclength g) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (radialArclength_hasDerivAt g r).differentiableAt, ?_⟩
  have hd : deriv (radialArclength g) = fun r => Real.sqrt (axisRadialCoefficient g r) :=
    funext (fun r => (radialArclength_hasDerivAt g r).deriv)
  rw [hd]
  exact (axisRadialCoefficient_contDiff g).sqrt (fun r => (axisRadialCoefficient_pos g r).ne')

/-- Section 12.6: the arclength coordinate retains the smooth odd tip parity. -/
theorem radialArclength_odd : Function.Odd (radialArclength g) := by
  intro r
  have h := intervalIntegral.integral_comp_neg
    (fun s => Real.sqrt (axisRadialCoefficient g s)) (a := (0 : ℝ)) (b := r)
  have he (s : ℝ) : Real.sqrt (axisRadialCoefficient g (-s)) =
      Real.sqrt (axisRadialCoefficient g s) :=
    congrArg Real.sqrt (axisRadialCoefficient_even g hrotation s)
  simp_rw [he] at h
  rw [neg_zero, intervalIntegral.integral_symm 0 (-r)] at h
  change radialArclength g r = -radialArclength g (-r) at h
  linarith only [h]

/-- Section 12.6: completeness gives the entire signed intrinsic axis. -/
theorem radialArclength_surjective (hcomplete : MetricComplete g) :
    Function.Surjective (radialArclength g) := by
  intro s
  by_cases hs : 0 ≤ s
  · obtain ⟨r, _, hr⟩ := exists_radialArclength_eq g hcomplete hs
    exact ⟨r, hr⟩
  · obtain ⟨r, _, hr⟩ := exists_radialArclength_eq g hcomplete (neg_nonneg.mpr (le_of_not_ge hs))
    exact ⟨-r, by rw [radialArclength_odd g hrotation, hr, neg_neg]⟩

/-- Section 12.6: the monotone coordinate keeps its actual integral as forward map. -/
noncomputable def radialArclengthOrderIso (hcomplete : MetricComplete g) : ℝ ≃o ℝ :=
  (radialArclength_strictMono g).orderIsoOfSurjective (radialArclength g)
    (radialArclength_surjective g hrotation hcomplete)

theorem radialArclengthOrderIso_apply (hcomplete : MetricComplete g) (r : ℝ) :
    radialArclengthOrderIso g hrotation hcomplete r = radialArclength g r := rfl

/-- Section 12.6: the actual inverse coordinate is smooth, with no puncture at zero. -/
theorem radialArclengthOrderIso_symm_contDiff (hcomplete : MetricComplete g) :
    ContDiff ℝ ∞ ((radialArclengthOrderIso g hrotation hcomplete).symm : ℝ → ℝ) := by
  let Φ := (radialArclengthOrderIso g hrotation hcomplete).toHomeomorph
  exact Φ.contDiff_symm_deriv
    (fun r => (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne')
    (radialArclength_hasDerivAt g) (radialArclength_contDiff g)

/-- Section 12.6: the signed intrinsic axis is an actual smooth diffeomorphism. -/
noncomputable def radialArclengthDiffeomorph (hcomplete : MetricComplete g) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := (radialArclengthOrderIso g hrotation hcomplete).toEquiv
  contMDiff_toFun := (radialArclength_contDiff g).contMDiff
  contMDiff_invFun := (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete).contMDiff

theorem radialArclengthOrderIso_symm_zero (hcomplete : MetricComplete g) :
    (radialArclengthOrderIso g hrotation hcomplete).symm 0 = 0 := by
  apply (radialArclengthOrderIso g hrotation hcomplete).injective
  rw [OrderIso.apply_symm_apply, radialArclengthOrderIso_apply, radialArclength_zero]

/-- Section 12.6: the smooth inverse retains odd parity, including the tip. -/
theorem radialArclengthOrderIso_symm_odd (hcomplete : MetricComplete g) :
    Function.Odd ((radialArclengthOrderIso g hrotation hcomplete).symm : ℝ → ℝ) := by
  intro s
  apply (radialArclengthOrderIso g hrotation hcomplete).injective
  rw [OrderIso.apply_symm_apply, radialArclengthOrderIso_apply,
    radialArclength_odd g hrotation]
  change -s = -(radialArclengthOrderIso g hrotation hcomplete
    ((radialArclengthOrderIso g hrotation hcomplete).symm s))
  rw [OrderIso.apply_symm_apply]

/-- Section 12.6: the inverse derivative is the reciprocal actual radial speed. -/
theorem radialArclengthOrderIso_symm_hasDerivAt (hcomplete : MetricComplete g) (s : ℝ) :
    HasDerivAt (radialArclengthOrderIso g hrotation hcomplete).symm
      (Real.sqrt (axisRadialCoefficient g
        ((radialArclengthOrderIso g hrotation hcomplete).symm s)))⁻¹ s := by
  let Φ := (radialArclengthOrderIso g hrotation hcomplete).toHomeomorph
  exact Φ.toOpenPartialHomeomorph.hasDerivAt_symm
    (mem_univ s) (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g (Φ.symm s))).ne'
    (radialArclength_hasDerivAt g (Φ.symm s))

end PoincareMT.M35.Uniqueness
