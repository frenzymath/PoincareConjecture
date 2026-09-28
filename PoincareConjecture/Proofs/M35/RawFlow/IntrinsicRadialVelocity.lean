import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicTip
import PoincareConjecture.Proofs.M35.CapGeometry.RadialSectionalPlane
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds











set_option autoImplicit false

open Set MeasureTheory
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

private theorem warping_second_contDiff :
    ContDiff ℝ ∞ (deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete))) :=
  (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp (intrinsicWarpingRadius_contDiff g hrotation hcomplete)).2).2

private theorem warping_second_odd :
    Function.Odd (deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete))) :=
  deriv_odd_of_even
    ((contDiff_infty_iff_deriv.mp
      (intrinsicWarpingRadius_contDiff g hrotation hcomplete)).2.differentiable (by simp))
    (deriv_even_of_odd
      ((intrinsicWarpingRadius_contDiff g hrotation hcomplete).differentiable (by simp))
      (intrinsicWarpingRadius_odd g hrotation hcomplete))


noncomputable def intrinsicRadialAcceleration (s : ℝ) : ℝ :=
  2 * axisDivision (deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete))) s /
    intrinsicWarpingQuotient g hrotation hcomplete s

theorem intrinsicRadialAcceleration_contDiff :
    ContDiff ℝ ∞ (intrinsicRadialAcceleration g hrotation hcomplete) :=
  (contDiff_const.mul (axisDivision_contDiff (warping_second_contDiff g hrotation hcomplete))).div
    (intrinsicWarpingQuotient_contDiff g hrotation hcomplete)
    (fun s => (intrinsicWarpingQuotient_pos g hrotation hcomplete s).ne')

theorem intrinsicRadialAcceleration_even :
    Function.Even (intrinsicRadialAcceleration g hrotation hcomplete) := by
  intro s
  rw [intrinsicRadialAcceleration, intrinsicRadialAcceleration,
    axisDivision_even_of_odd (warping_second_contDiff g hrotation hcomplete)
      (warping_second_odd g hrotation hcomplete) s,
    intrinsicWarpingQuotient_even g hrotation hcomplete s]


theorem intrinsicRadialAcceleration_eq {s : ℝ} (hs : 0 < s) :
    intrinsicRadialAcceleration g hrotation hcomplete s =
      2 * deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) s /
        intrinsicWarpingRadius g hrotation hcomplete s := by
  let f := intrinsicWarpingRadius g hrotation hcomplete
  have hz : deriv (deriv f) 0 = 0 := by
    have hh := warping_second_odd g hrotation hcomplete 0
    rw [neg_zero] at hh
    linarith only [hh]
  have hn : s * axisDivision (deriv (deriv f)) s = deriv (deriv f) s := by
    rw [mul_axisDivision (warping_second_contDiff g hrotation hcomplete), hz, sub_zero]
  apply (div_eq_div_iff (intrinsicWarpingQuotient_pos g hrotation hcomplete s).ne'
    (intrinsicWarpingRadius_pos g hrotation hcomplete hs).ne').mpr
  change 2 * axisDivision (deriv (deriv f)) s * f s =
    2 * deriv (deriv f) s * intrinsicWarpingQuotient g hrotation hcomplete s
  rw [← hn, show f s = s * intrinsicWarpingQuotient g hrotation hcomplete s from
    (mul_intrinsicWarpingQuotient g hrotation hcomplete s).symm]
  ring


theorem intrinsicRadialAcceleration_eq_sectional {s : ℝ} (hs : 0 < s) :
    intrinsicRadialAcceleration g hrotation hcomplete s =
      -2 * (radialMixedCurvatureFactor g
        ((radialArclengthOrderIso g hrotation hcomplete).symm s) /
          axisRadialCoefficient g ((radialArclengthOrderIso g hrotation hcomplete).symm s)) := by
  rw [intrinsicRadialAcceleration_eq g hrotation hcomplete hs,
    (intrinsicWarpingRadius_deriv_hasDerivAt g hrotation hcomplete hs).deriv,
    radialMixedCurvatureFactor_eq_warping g
      (radialArclengthOrderIso_symm_pos g hrotation hcomplete hs)]
  unfold intrinsicWarpingRadius
  ring


noncomputable def intrinsicRadialVelocity (s : ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..s, intrinsicRadialAcceleration g hrotation hcomplete a

theorem intrinsicRadialVelocity_hasDerivAt (s : ℝ) :
    HasDerivAt (intrinsicRadialVelocity g hrotation hcomplete)
      (intrinsicRadialAcceleration g hrotation hcomplete s) s := by
  have hc := (intrinsicRadialAcceleration_contDiff g hrotation hcomplete).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem intrinsicRadialVelocity_contDiff :
    ContDiff ℝ ∞ (intrinsicRadialVelocity g hrotation hcomplete) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s =>
    (intrinsicRadialVelocity_hasDerivAt g hrotation hcomplete s).differentiableAt, ?_⟩
  have hd : deriv (intrinsicRadialVelocity g hrotation hcomplete) =
      intrinsicRadialAcceleration g hrotation hcomplete :=
    funext (fun s => (intrinsicRadialVelocity_hasDerivAt g hrotation hcomplete s).deriv)
  rw [hd]
  exact intrinsicRadialAcceleration_contDiff g hrotation hcomplete

theorem intrinsicRadialVelocity_zero : intrinsicRadialVelocity g hrotation hcomplete 0 = 0 := by
  simp only [intrinsicRadialVelocity, intervalIntegral.integral_same]

theorem intrinsicRadialVelocity_odd :
    Function.Odd (intrinsicRadialVelocity g hrotation hcomplete) := by
  intro s
  have h := intervalIntegral.integral_comp_neg
    (intrinsicRadialAcceleration g hrotation hcomplete) (a := (0 : ℝ)) (b := s)
  have he (a : ℝ) : intrinsicRadialAcceleration g hrotation hcomplete (-a) =
      intrinsicRadialAcceleration g hrotation hcomplete a :=
    intrinsicRadialAcceleration_even g hrotation hcomplete a
  simp_rw [he] at h
  rw [neg_zero, intervalIntegral.integral_symm 0 (-s)] at h
  change intrinsicRadialVelocity g hrotation hcomplete s =
    -intrinsicRadialVelocity g hrotation hcomplete (-s) at h
  linarith only [h]


theorem intrinsicRadialVelocity_quotient_contDiff_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (fun x : E => axisDivision (intrinsicRadialVelocity g hrotation hcomplete) ‖x‖) :=
  contDiff_even_norm
    (axisDivision_contDiff (intrinsicRadialVelocity_contDiff g hrotation hcomplete))
    (axisDivision_even_of_odd (intrinsicRadialVelocity_contDiff g hrotation hcomplete)
      (intrinsicRadialVelocity_odd g hrotation hcomplete))

end PoincareConjecture.M35.Uniqueness
