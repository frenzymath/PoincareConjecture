import PoincareConjecture.Proofs.M35.Uniqueness.RadialArclength
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.M35.Uniqueness

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

theorem radialArclength_contDiff : ContDiff ℝ ∞ (radialArclength g) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (radialArclength_hasDerivAt g r).differentiableAt, ?_⟩
  have hd : deriv (radialArclength g) = fun r => Real.sqrt (axisRadialCoefficient g r) :=
    funext (fun r => (radialArclength_hasDerivAt g r).deriv)
  rw [hd]
  exact (axisRadialCoefficient_contDiff g).sqrt (fun r => (axisRadialCoefficient_pos g r).ne')

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

theorem radialArclength_surjective (hcomplete : MetricComplete g) :
    Function.Surjective (radialArclength g) := by
  intro s
  by_cases hs : 0 ≤ s
  · obtain ⟨r, _, hr⟩ := exists_radialArclength_eq g hcomplete hs
    exact ⟨r, hr⟩
  · obtain ⟨r, _, hr⟩ := exists_radialArclength_eq g hcomplete (neg_nonneg.mpr (le_of_not_ge hs))
    exact ⟨-r, by rw [radialArclength_odd g hrotation, hr, neg_neg]⟩

noncomputable def radialArclengthOrderIso (hcomplete : MetricComplete g) : ℝ ≃o ℝ :=
  (radialArclength_strictMono g).orderIsoOfSurjective (radialArclength g)
    (radialArclength_surjective g hrotation hcomplete)

theorem radialArclengthOrderIso_apply (hcomplete : MetricComplete g) (r : ℝ) :
    radialArclengthOrderIso g hrotation hcomplete r = radialArclength g r := rfl

theorem radialArclengthOrderIso_symm_contDiff (hcomplete : MetricComplete g) :
    ContDiff ℝ ∞ ((radialArclengthOrderIso g hrotation hcomplete).symm : ℝ → ℝ) := by
  let Φ := (radialArclengthOrderIso g hrotation hcomplete).toHomeomorph
  exact Φ.contDiff_symm_deriv
    (fun r => (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne')
    (radialArclength_hasDerivAt g) (radialArclength_contDiff g)

noncomputable def radialArclengthDiffeomorph (hcomplete : MetricComplete g) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := (radialArclengthOrderIso g hrotation hcomplete).toEquiv
  contMDiff_toFun := (radialArclength_contDiff g).contMDiff
  contMDiff_invFun := (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete).contMDiff

theorem radialArclengthOrderIso_symm_zero (hcomplete : MetricComplete g) :
    (radialArclengthOrderIso g hrotation hcomplete).symm 0 = 0 := by
  apply (radialArclengthOrderIso g hrotation hcomplete).injective
  rw [OrderIso.apply_symm_apply, radialArclengthOrderIso_apply, radialArclength_zero]

theorem radialArclengthOrderIso_symm_odd (hcomplete : MetricComplete g) :
    Function.Odd ((radialArclengthOrderIso g hrotation hcomplete).symm : ℝ → ℝ) := by
  intro s
  apply (radialArclengthOrderIso g hrotation hcomplete).injective
  rw [OrderIso.apply_symm_apply, radialArclengthOrderIso_apply,
    radialArclength_odd g hrotation]
  change -s = -(radialArclengthOrderIso g hrotation hcomplete
    ((radialArclengthOrderIso g hrotation hcomplete).symm s))
  rw [OrderIso.apply_symm_apply]

theorem radialArclengthOrderIso_symm_hasDerivAt (hcomplete : MetricComplete g) (s : ℝ) :
    HasDerivAt (radialArclengthOrderIso g hrotation hcomplete).symm
      (Real.sqrt (axisRadialCoefficient g
        ((radialArclengthOrderIso g hrotation hcomplete).symm s)))⁻¹ s := by
  let Φ := (radialArclengthOrderIso g hrotation hcomplete).toHomeomorph
  exact Φ.toOpenPartialHomeomorph.hasDerivAt_symm
    (mem_univ s) (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g (Φ.symm s))).ne'
    (radialArclength_hasDerivAt g (Φ.symm s))

end PoincareConjecture.M35.Uniqueness
