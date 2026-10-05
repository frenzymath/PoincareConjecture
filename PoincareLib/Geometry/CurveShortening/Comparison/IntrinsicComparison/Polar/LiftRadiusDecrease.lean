import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Local.PolarCurveLift
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Unit.TangentIndependence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.AffineSpace.Ordered

/-! The acute terminal angle makes the actual inverse lift shorter to the left.
Source: MT Claim 19.41, p. 471; short-geodesic-digons derivation, Section 8.
Gauss' identity is applied to the real lifted curve, including at the endpoint. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- An acute normalized metric angle forces the original unnormalized
pairing to be positive. No extra nonzero-vector premise is needed.
Source: MT Claim 19.41, p. 471; digon derivation, Section 8. -/
theorem m64Intrinsic_inner_pos_of_cornerAngle_acute
    (G : RiemannianMetric 2 AnnulusCoordinates) (p v w : AnnulusCoordinates)
    (hangle : G.cornerAngle p v w < Real.pi / 2) : 0 < G.inner p v w := by
  have h := Real.arccos_lt_pi_div_two.mp hangle
  change 0 < G.inner p ((Real.sqrt (G.inner p v v))⁻¹ • v)
    ((Real.sqrt (G.inner p w w))⁻¹ • w) at h
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  exact pos_of_mul_pos_right
    (pos_of_mul_pos_right h (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Gauss' identity identifies the derivative of the lifted squared
radius with its actual terminal radial pairing.
Source: MT Claim 19.41, p. 471; digon derivation, Section 8. -/
theorem m64Intrinsic_polar_lift_norm_sq_derivative
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {u beta : ℝ → AnnulusCoordinates}
    {s : ℝ} {du db : AnnulusCoordinates}
    (he : DifferentiableAt ℝ e (u s)) (hu : HasDerivAt u du s) (hb : HasDerivAt beta db s)
    (hlift : (fun a => e (u a)) =ᶠ[𝓝 s] beta)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (u s) (u s) w = inner ℝ (u s) w) :
    HasDerivAt (fun a => ‖u a‖ ^ 2)
      (2 * N.metric.inner (e (u s)) (fderiv ℝ e (u s) (u s)) db) s := by
  have hd : fderiv ℝ e (u s) du = db :=
    ((he.hasFDerivAt.comp_hasDerivAt s hu).congr_of_eventuallyEq hlift.symm).unique hb
  have hpair : N.metric.euclideanCoefficients (e (u s))
      (fderiv ℝ e (u s) (u s)) db = inner ℝ (u s) du := by
    rw [← hd]
    simpa only [RiemannianMetric.euclideanCoefficients,
      RiemannianMetric.pullbackCoefficients, ContinuousLinearMap.bilinearComp_apply,
      mfderiv_eq_fderiv] using! hgauss du
  change HasDerivAt (fun a => ‖u a‖ ^ 2)
    (2 * N.metric.euclideanCoefficients (e (u s)) (fderiv ℝ e (u s) (u s)) db) s
  rw [hpair]
  exact hu.norm_sq

/-- An acute terminal pairing gives strictly smaller lifted radius for
nearby earlier parameters, including when the original radius saturates
the allowed bound. This assertion does not assume confinement of the lift.
Source: MT Claim 19.41, p. 471; digon derivation, Section 8. -/
theorem m64Intrinsic_polar_lift_radius_decreases_left
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {u beta : ℝ → AnnulusCoordinates}
    {s : ℝ} {du db : AnnulusCoordinates}
    (he : DifferentiableAt ℝ e (u s)) (hu : HasDerivAt u du s) (hb : HasDerivAt beta db s)
    (hlift : (fun a => e (u a)) =ᶠ[𝓝 s] beta)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (u s) (u s) w = inner ℝ (u s) w)
    (hangle : N.metric.cornerAngle (e (u s))
      (fderiv ℝ e (u s) (u s)) db < Real.pi / 2) :
    ∀ᶠ a in 𝓝[<] s, ‖u a‖ < ‖u s‖ := by
  have hd := m64Intrinsic_polar_lift_norm_sq_derivative N he hu hb hlift hgauss
  have hpos : 0 < 2 * N.metric.inner (e (u s)) (fderiv ℝ e (u s) (u s)) db :=
    mul_pos (by norm_num) (m64Intrinsic_inner_pos_of_cornerAngle_acute N.metric
      (e (u s)) (fderiv ℝ e (u s) (u s)) db hangle)
  have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  filter_upwards [hlim.eventually (Ioi_mem_nhds hpos), self_mem_nhdsWithin] with a ha has
  have hsq : ‖u a‖ ^ 2 < ‖u s‖ ^ 2 := (slope_pos_iff_gt has).mp ha
  nlinarith only [hsq, norm_nonneg (u a), norm_nonneg (u s)]

end PoincareMT
