import PoincareConjecture.Proofs.M35.TerminalBlowup.AngularCollapse

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hsec : D.NonnegativeSectionalCurvature)

include D hrotation hsec

theorem axisWarpingSecond_nonpos {r : ℝ} (hr : 0 < r) :
    axisWarpingSecond g r ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (axisWarpingRadius_pos g hr).le)
      (radialMixedCurvatureFactor_nonneg D hrotation hsec hr)
  · exact (axisRadialCoefficient_pos g r).le

theorem axisWarpingSlope_nonneg (hcomplete : MetricComplete g)
    {r : ℝ} (hr : 0 < r) : 0 ≤ axisWarpingSlope g r :=
  weighted_radial_derivative_nonneg
    (fun _ hu => axisWarpingRadius_pos g hu)
    (fun _ hu => axisWarpingRadius_hasDerivAt g hu)
    (fun _ hu => axisWarpingSlope_hasDerivAt g hu)
    (fun u _ => radialArclength_hasDerivAt g u)
    (fun u _ => axisRadialSpeed_pos g u)
    (radialArclength_tendsto_atTop g hcomplete)
    (fun _ hu => axisWarpingSecond_nonpos D hrotation hsec hu) hr

theorem axisWarpingSlope_le_one {r : ℝ} (hr : 0 < r) :
    axisWarpingSlope g r ≤ 1 := by
  let e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1
  have h := hsec (r • e 2) (e 0) (e 1)
  rw [(rotational_sectional_numerators_axis D hrotation hr).1] at h
  have hfactor := nonneg_of_mul_nonneg_right h (axisAngularCoefficient_pos g r)
  have hquot := div_nonneg hfactor (axisAngularCoefficient_pos g r).le
  rw [radialTangentialCurvatureFactor_eq_warping g hr] at hquot
  have hnum : 0 ≤ 1 - axisWarpingSlope g r ^ 2 := by
    have h := mul_nonneg hquot (sq_nonneg (axisWarpingRadius g r))
    simpa only [div_mul_cancel₀ _
      (sq_pos_of_pos (axisWarpingRadius_pos g hr)).ne'] using h
  nlinarith

theorem axisWarpingRadius_monotoneOn (hcomplete : MetricComplete g) :
    MonotoneOn (axisWarpingRadius g) (Ioi 0) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (fun _ hu => (axisWarpingRadius_hasDerivAt g hu).continuousAt.continuousWithinAt)
    (fun _ hu => (axisWarpingRadius_hasDerivAt g (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => mul_nonneg (axisRadialSpeed_pos g u).le
      (axisWarpingSlope_nonneg D hrotation hsec hcomplete (interior_subset hu)))

theorem scalar_mul_axisWarpingRadius_sq_ge {r : ℝ} (hr : 0 < r) :
    2 * (1 - axisWarpingSlope g r ^ 2) ≤
      D.scalarCurvature (r • EuclideanSpace.single (2 : Fin 3) 1) *
        axisWarpingRadius g r ^ 2 := by
  have hrad := div_nonneg (radialMixedCurvatureFactor_nonneg D hrotation hsec hr)
    (axisRadialCoefficient_pos g r).le
  have hscalar := rotational_scalar_axis D hrotation hr
  have hangular : 2 * (1 - axisWarpingSlope g r ^ 2) / axisWarpingRadius g r ^ 2 ≤
      D.scalarCurvature (r • EuclideanSpace.single (2 : Fin 3) 1) := by
    rw [hscalar]
    calc
      _ = 2 * (radialTangentialCurvatureFactor g r / axisAngularCoefficient g r) := by
        rw [radialTangentialCurvatureFactor_eq_warping g hr]
        ring
      _ ≤ 2 * (radialTangentialCurvatureFactor g r / axisAngularCoefficient g r) +
          4 * (radialMixedCurvatureFactor g r / axisRadialCoefficient g r) :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num) hrad)
      _ = _ := by ring
  exact (div_le_iff₀ (sq_pos_of_pos (axisWarpingRadius_pos g hr))).mp hangular

theorem axisWarpingSlope_antitoneOn : AntitoneOn (axisWarpingSlope g) (Ioi 0) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun _ hu => (axisWarpingSlope_hasDerivAt g hu).continuousAt.continuousWithinAt)
    (fun _ hu => (axisWarpingSlope_hasDerivAt g (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => mul_nonpos_of_nonneg_of_nonpos (axisRadialSpeed_pos g u).le
      (axisWarpingSecond_nonpos D hrotation hsec (interior_subset hu)))

theorem axisWarpingSlope_mul_arclength_le {r : ℝ} (hr : 0 < r) :
    axisWarpingSlope g r * radialArclength g r ≤ axisWarpingRadius g r := by
  let F (u : ℝ) := axisWarpingRadius g u - axisWarpingSlope g r * radialArclength g u
  have hf : Continuous (axisWarpingRadius g) :=
    continuous_id.mul (axisAngularCoefficient_contDiff g).continuous.sqrt
  have hs : Continuous (radialArclength g) :=
    continuous_iff_continuousAt.mpr (fun u => (radialArclength_hasDerivAt g u).continuousAt)
  have hF : Continuous F := hf.sub (continuous_const.mul hs)
  have hd (u : ℝ) (hu : 0 < u) : HasDerivAt F
      (axisRadialSpeed g u * (axisWarpingSlope g u - axisWarpingSlope g r)) u := by
    convert! (axisWarpingRadius_hasDerivAt g hu).sub
      ((radialArclength_hasDerivAt g u).const_mul (axisWarpingSlope g r)) using 1
    dsimp only [axisRadialSpeed]
    ring
  have hmono : MonotoneOn F (Icc 0 r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hF.continuousOn
      (fun u hu => by
        have hu' : u ∈ Ioo 0 r := by simpa only [interior_Icc] using hu
        exact (hd u hu'.1).hasDerivWithinAt)
      (fun u hu => by
        have hu' : u ∈ Ioo 0 r := by simpa only [interior_Icc] using hu
        exact mul_nonneg (axisRadialSpeed_pos g u).le (sub_nonneg.mpr
          (axisWarpingSlope_antitoneOn D hrotation hsec hu'.1 hr hu'.2.le)))
  have h := hmono ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr.le
  dsimp only [F] at h
  simpa only [axisWarpingRadius, zero_mul, radialArclength_zero,
    mul_zero, sub_zero, sub_nonneg] using h

theorem axisWarpingSlope_le_radius_div_arclength {r : ℝ} (hr : 0 < r) :
    axisWarpingSlope g r ≤ axisWarpingRadius g r / radialArclength g r := by
  have hs : 0 < radialArclength g r := by
    simpa only [radialArclength_zero] using radialArclength_strictMono g hr
  exact (le_div_iff₀ hs).mpr (axisWarpingSlope_mul_arclength_le D hrotation hsec hr)

end PoincareConjecture.M35.Uniqueness
