import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicRadialCoordinate
import PoincareConjecture.Proofs.M35.CapGeometry.RadialEndSlope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation in

theorem axisAngularCoefficient_zero_eq_radial :
    axisAngularCoefficient g 0 = axisRadialCoefficient g 0 := by
  let e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1
  obtain ⟨A, hA⟩ := exists_axis_rotation (e 0)
  have hnorm : ‖e 0‖ = 1 := by simp [e]
  rw [hnorm, one_smul] at hA
  change standardRotation A (e 2) = e 0 at hA
  have hz : standardRotation A (0 : StandardCapSpace) = 0 :=
    map_zero (Matrix.toEuclideanLin A.1)
  have h := hrotation A 0 (e 2) (e 2)
  rw [standardRotation_mfderiv] at h
  change g.euclideanCoefficients (standardRotation A 0)
    (standardRotation A (e 2)) (standardRotation A (e 2)) =
      g.euclideanCoefficients 0 (e 2) (e 2) at h
  change g.euclideanCoefficients (0 • e 2) (e 0) (e 0) =
    g.euclideanCoefficients (0 • e 2) (e 2) (e 2)
  simpa only [hz, hA, zero_smul] using h

theorem axisWarpingRadius_contDiff : ContDiff ℝ ∞ (axisWarpingRadius g) :=
  contDiff_id.mul ((axisAngularCoefficient_contDiff g).sqrt
    (fun r => (axisAngularCoefficient_pos g r).ne'))

variable (hcomplete : MetricComplete g)

noncomputable def intrinsicWarpingRadius (s : ℝ) : ℝ :=
  axisWarpingRadius g ((radialArclengthOrderIso g hrotation hcomplete).symm s)

theorem intrinsicWarpingRadius_contDiff :
    ContDiff ℝ ∞ (intrinsicWarpingRadius g hrotation hcomplete) :=
  (axisWarpingRadius_contDiff g).comp
    (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)

theorem intrinsicWarpingRadius_zero : intrinsicWarpingRadius g hrotation hcomplete 0 = 0 := by
  simp only [intrinsicWarpingRadius, radialArclengthOrderIso_symm_zero,
    axisWarpingRadius, zero_mul]

theorem intrinsicWarpingRadius_odd :
    Function.Odd (intrinsicWarpingRadius g hrotation hcomplete) := by
  intro s
  simp only [intrinsicWarpingRadius, axisWarpingRadius]
  rw [radialArclengthOrderIso_symm_odd g hrotation hcomplete s,
    axisAngularCoefficient_even g hrotation]
  ring

theorem radialArclengthOrderIso_symm_pos {s : ℝ} (hs : 0 < s) :
    0 < (radialArclengthOrderIso g hrotation hcomplete).symm s := by
  have h := (radialArclengthOrderIso g hrotation hcomplete).symm.strictMono hs
  rwa [radialArclengthOrderIso_symm_zero] at h

theorem intrinsicWarpingRadius_pos {s : ℝ} (hs : 0 < s) :
    0 < intrinsicWarpingRadius g hrotation hcomplete s :=
  axisWarpingRadius_pos g (radialArclengthOrderIso_symm_pos g hrotation hcomplete hs)

theorem intrinsicWarpingRadius_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (intrinsicWarpingRadius g hrotation hcomplete)
      (axisWarpingSlope g ((radialArclengthOrderIso g hrotation hcomplete).symm s)) s := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hr : 0 < r := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  have hd := (axisWarpingRadius_hasDerivAt g hr).comp s
    (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete s)
  convert! hd using 1
  change axisWarpingSlope g r = Real.sqrt (axisRadialCoefficient g r) *
    axisWarpingSlope g r * (Real.sqrt (axisRadialCoefficient g r))⁻¹
  field_simp [(Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne']

theorem intrinsicWarpingRadius_deriv_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (deriv (intrinsicWarpingRadius g hrotation hcomplete))
      (axisWarpingSecond g ((radialArclengthOrderIso g hrotation hcomplete).symm s)) s := by
  let q := (radialArclengthOrderIso g hrotation hcomplete).symm
  have hr : 0 < q s := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  have hd : HasDerivAt (fun a => axisWarpingSlope g (q a))
      (axisWarpingSecond g (q s)) s := by
    convert! (axisWarpingSlope_hasDerivAt g hr).comp s
      (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete s) using 1
    change axisWarpingSecond g (q s) = Real.sqrt (axisRadialCoefficient g (q s)) *
      axisWarpingSecond g (q s) * (Real.sqrt (axisRadialCoefficient g (q s)))⁻¹
    field_simp [(Real.sqrt_pos.mpr (axisRadialCoefficient_pos g (q s))).ne']
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with a ha
  exact (intrinsicWarpingRadius_hasDerivAt g hrotation hcomplete ha).deriv

theorem intrinsicWarpingRadius_hasDerivAt_zero :
    HasDerivAt (intrinsicWarpingRadius g hrotation hcomplete) 1 0 := by
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) 0).hasDerivAt
  have hd : HasDerivAt (axisWarpingRadius g) (Real.sqrt (axisAngularCoefficient g 0)) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).mul (ha.sqrt (axisAngularCoefficient_pos g 0).ne') using 1
    simp only [id_eq, one_mul, zero_mul, add_zero]
  have hd' : HasDerivAt (axisWarpingRadius g) (Real.sqrt (axisAngularCoefficient g 0))
      ((radialArclengthOrderIso g hrotation hcomplete).symm 0) := by
    rwa [radialArclengthOrderIso_symm_zero]
  have hc := hd'.comp 0 (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete 0)
  rw [radialArclengthOrderIso_symm_zero, axisAngularCoefficient_zero_eq_radial g hrotation,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g 0)).ne'] at hc
  exact hc

theorem rotational_scalar_eq_intrinsicWarping (D : LeviCivitaData g)
    {s : ℝ} (hs : 0 < s) :
    D.scalarCurvature ((radialArclengthOrderIso g hrotation hcomplete).symm s •
      EuclideanSpace.single (2 : Fin 3) 1) =
      2 * (1 - deriv (intrinsicWarpingRadius g hrotation hcomplete) s ^ 2) /
          intrinsicWarpingRadius g hrotation hcomplete s ^ 2 -
        4 * deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) s /
          intrinsicWarpingRadius g hrotation hcomplete s := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hr : 0 < r := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  rw [(intrinsicWarpingRadius_hasDerivAt g hrotation hcomplete hs).deriv,
    (intrinsicWarpingRadius_deriv_hasDerivAt g hrotation hcomplete hs).deriv,
    rotational_scalar_axis D hrotation hr]
  change _ = 2 * (1 - axisWarpingSlope g r ^ 2) / axisWarpingRadius g r ^ 2 -
    4 * axisWarpingSecond g r / axisWarpingRadius g r
  calc
    _ = 2 * (radialTangentialCurvatureFactor g r / axisAngularCoefficient g r) +
        4 * (radialMixedCurvatureFactor g r / axisRadialCoefficient g r) := by ring
    _ = _ := by
      rw [radialTangentialCurvatureFactor_eq_warping g hr,
        radialMixedCurvatureFactor_eq_warping g hr]
      ring

end PoincareConjecture.M35.Uniqueness
