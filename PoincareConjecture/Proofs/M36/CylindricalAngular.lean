import PoincareConjecture.Proofs.M36.CylindricalRadial
import PoincareConjecture.Proofs.M36.RadialEquality
import PoincareConjecture.Proofs.M36.PolarInverse

set_option autoImplicit false

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.M36

theorem cylindrical_vertical_velocity (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => g₀.cylindrical_end.coordinate (theta, s))
      ((radialSpeed g₀ ‖g₀.cylindrical_end.coordinate (theta, t)‖)⁻¹ •
        (‖g₀.cylindrical_end.coordinate (theta, t)‖⁻¹ •
          g₀.cylindrical_end.coordinate (theta, t))) t := by
  let gamma : ℝ → StandardCapSpace := fun s => g₀.cylindrical_end.coordinate (theta, s)
  have hx : gamma t ≠ 0 := cylindrical_coordinate_ne_zero g₀ (theta, t) ht.le
  have hd : DifferentiableAt ℝ gamma t :=
    (cylindrical_vertical_contMDiffAt g₀ theta ht.le).contDiffAt.differentiableAt (by simp)
  have hspeed := cylindrical_vertical_speed g₀ theta ht.le
  have hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1 = deriv gamma t := by
    rw [mfderiv_eq_fderiv]
    rfl
  change Real.sqrt (g₀.metric.inner (gamma t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1)) = 1 at hspeed
  rw [hv] at hspeed
  have hmetric : g₀.metric.inner (gamma t) (deriv gamma t) (deriv gamma t) = 1 :=
    Real.sqrt_eq_one.mp hspeed
  have heq : (fun s => radialArclength g₀ ‖gamma s‖) =ᶠ[nhds t]
      (fun s => g₀.cylindrical_end.radius + s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact cylindrical_radial_height g₀ (theta, s) hs.le
  have hlinear : HasDerivAt (fun s : ℝ => g₀.cylindrical_end.radius + s) 1 t := by
    convert! (hasDerivAt_id t).const_add g₀.cylindrical_end.radius using 1
  have hradial := (radial_path_hasDerivAt g₀ hd.hasDerivAt hx).unique
    (hlinear.congr_of_eventuallyEq heq)
  exact hd.hasDerivAt.congr_deriv (unit_velocity_of_radial_derivative_one g₀ hx hmetric hradial)

theorem cylindrical_normalized_hasDerivAt (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ‖g₀.cylindrical_end.coordinate (theta, s)‖⁻¹ •
      g₀.cylindrical_end.coordinate (theta, s)) 0 t := by
  let gamma : ℝ → StandardCapSpace := fun s => g₀.cylindrical_end.coordinate (theta, s)
  let q := ‖gamma t‖
  let a := (radialSpeed g₀ q)⁻¹
  let u := q⁻¹ • gamma t
  have hx : gamma t ≠ 0 := cylindrical_coordinate_ne_zero g₀ (theta, t) ht.le
  have hq : q ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖u‖ = 1 := by simp [u, q, norm_smul, norm_ne_zero_iff.mpr hx]
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hg : HasDerivAt gamma (a • u) t := cylindrical_vertical_velocity g₀ theta ht
  have hnorm : HasDerivAt (fun s => ‖gamma s‖) a t := by
    have h := norm_path_hasDerivAt hg hx
    change HasDerivAt (fun s => ‖gamma s‖) (inner ℝ u (a • u)) t at h
    simpa only [real_inner_smul_right, huu, mul_one] using h
  apply ((hnorm.inv hq).smul hg).congr_deriv
  change q⁻¹ • (a • (q⁻¹ • gamma t)) + (-a / q ^ 2) • gamma t = 0
  have hc : q⁻¹ * (a * q⁻¹) + (-a / q ^ 2) = 0 := by
    field_simp
    ring
  simp only [smul_smul, ← add_smul, hc, zero_smul]

theorem cylindrical_normalized_eq_zero_slice (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {t : ℝ} (ht : 0 ≤ t) :
    ‖g₀.cylindrical_end.coordinate (theta, t)‖⁻¹ • g₀.cylindrical_end.coordinate (theta, t) =
      ‖g₀.cylindrical_end.coordinate (theta, 0)‖⁻¹ •
        g₀.cylindrical_end.coordinate (theta, 0) := by
  let gamma : ℝ → StandardCapSpace := fun s => g₀.cylindrical_end.coordinate (theta, s)
  let N : ℝ → StandardCapSpace := fun s => ‖gamma s‖⁻¹ • gamma s
  have hgamma : ContinuousOn gamma (Set.Icc 0 t) := fun s hs =>
    (cylindrical_vertical_contMDiffAt g₀ theta hs.1).continuousAt.continuousWithinAt
  have hcont : ContinuousOn N (Set.Icc 0 t) :=
    (hgamma.norm.inv₀ (fun s hs => norm_ne_zero_iff.mpr
      (cylindrical_coordinate_ne_zero g₀ (theta, s) hs.1))).smul hgamma
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le ht hcont
    (show DifferentiableOn ℝ N (Set.Ioo 0 t) from fun s hs =>
      (cylindrical_normalized_hasDerivAt g₀ theta hs.1).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun s hs => by
      rw [(cylindrical_normalized_hasDerivAt g₀ theta hs.1).deriv]
      simp)
    (intervalIntegrable_const (c := (0 : ℝ)))
  have heq : N t - N 0 = 0 := by simpa using hbound
  exact sub_eq_zero.mp heq

noncomputable def cylindricalBoundaryDirection (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) : UnitTwoSphere :=
  radialDirection (g₀.cylindrical_end.coordinate (theta, 0))

theorem cylindrical_coordinate_radial (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    g₀.cylindrical_end.coordinate z =
      radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + z.2) •
        (cylindricalBoundaryDirection g₀ z.1).1 := by
  have hx := cylindrical_coordinate_ne_zero g₀ z hz
  have hx0 := cylindrical_coordinate_ne_zero g₀ (z.1, 0) le_rfl
  calc
    _ = ‖g₀.cylindrical_end.coordinate z‖ •
        (‖g₀.cylindrical_end.coordinate z‖⁻¹ • g₀.cylindrical_end.coordinate z) := by
      simp [smul_smul, norm_ne_zero_iff.mpr hx]
    _ = radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + z.2) •
        (‖g₀.cylindrical_end.coordinate (z.1, 0)‖⁻¹ •
          g₀.cylindrical_end.coordinate (z.1, 0)) := by
      rw [cylindrical_normalized_eq_zero_slice g₀ z.1 hz, cylindrical_coordinate_norm g₀ z hz]
    _ = _ := by rw [cylindricalBoundaryDirection, radialDirection_val _ hx0]

end PoincareConjecture.M36
