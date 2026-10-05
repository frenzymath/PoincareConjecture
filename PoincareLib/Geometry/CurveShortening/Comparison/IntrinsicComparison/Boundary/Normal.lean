import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Focusing.Endpoint

/-!
# The smooth inward normal along the first annulus boundary

Metric duality sends the radial covector to a transverse vector pointing
towards increasing Euclidean radius. Normalizing it gives the initial
velocity for the inward normal geodesic family in Claim 19.37.

Context: Morgan--Tian Claim 19.37, printed pp. 468-469, in the proof of Proposition
19.35.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The actual circle position has Euclidean squared norm equal to radius squared.
Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_boundary_self_inner (radius t : ℝ) :
    inner ℝ (intrinsicAnnulusBoundary radius t) (intrinsicAnnulusBoundary radius t) =
      radius ^ 2 := by
  calc
    _ = radius ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by
      simp only [intrinsicAnnulusBoundary, PiLp.inner_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.inner_apply]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- The Euclidean radial position is orthogonal to the actual circle velocity.
Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_boundary_radial_pairing (radius t : ℝ) :
    inner ℝ (intrinsicAnnulusBoundary radius t)
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) t) = 0 := by
  rw [m64Intrinsic_boundary_velocity]
  simp only [intrinsicAnnulusBoundary, PiLp.inner_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.inner_apply]
  ring

/-- A circle of nonzero radius never has the zero position vector. Source/construction:
Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_boundary_ne_zero {radius : ℝ} (hradius : radius ≠ 0) (t : ℝ) :
    intrinsicAnnulusBoundary radius t ≠ 0 := by
  intro hzero
  have h := m64Intrinsic_boundary_self_inner radius t
  rw [hzero, inner_zero_left] at h
  exact hradius (sq_eq_zero_iff.mp h.symm)

/-- Every intrinsic circle has a smooth unit normal orthogonal to its actual velocity and
pointing towards increasing Euclidean radius. For radius one this is the inward normal of
the annulus. Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_exists_smooth_inward_boundary_normal
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) :
    ∃ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal ∧
      ∀ t : ℝ,
        N.metric.inner (intrinsicAnnulusBoundary radius t) (normal t) (normal t) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary radius t) (normal t)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) t) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary radius t) (normal t) := by
  let gamma := intrinsicAnnulusBoundary radius
  let B := fun t => N.metric.euclideanCoefficients (gamma t)
  let V : ℝ → AnnulusCoordinates := fun t => (B t).inverse (innerSL ℝ (gamma t))
  have hgamma := m64Intrinsic_contDiff_boundary radius
  have hB : ContDiff ℝ ∞ B :=
    (contDiff_iff_contDiffAt.mpr N.metric.contDiffAt_euclideanCoefficients).comp hgamma
  have hBi (t : ℝ) : (B t).IsInvertible := N.metric.inner_isInvertible (gamma t)
  have hBinv : ContDiff ℝ ∞ (fun t => (B t).inverse) :=
    contDiff_iff_contDiffAt.mpr fun t => (hBi t).contDiffAt_map_inverse.comp t hB.contDiffAt
  have hV : ContDiff ℝ ∞ V := hBinv.clm_apply ((innerSL ℝ).contDiff.comp hgamma)
  have hdual (t : ℝ) (w : AnnulusCoordinates) :
      N.metric.inner (gamma t) (V t) w = inner ℝ (gamma t) w := by
    have h := congrArg (fun L : AnnulusCoordinates →L[ℝ] ℝ => L w)
      ((hBi t).self_apply_inverse (innerSL ℝ (gamma t)))
    exact h
  have hVne (t : ℝ) : V t ≠ 0 := by
    intro hz
    have h := hdual t (gamma t)
    rw [hz, map_zero, zero_apply] at h
    exact m64Intrinsic_boundary_ne_zero hradius t (inner_self_eq_zero.mp h.symm)
  have hVV (t : ℝ) : 0 < N.metric.inner (gamma t) (V t) (V t) :=
    N.metric.pos _ _ (hVne t)
  let speed : ℝ → ℝ := fun t => N.metric.tangentNorm (gamma t) (V t)
  have hspeed (t : ℝ) : 0 < speed t := Real.sqrt_pos.mpr (hVV t)
  have hsmooth : ContDiff ℝ ∞ speed :=
    ((hB.clm_apply hV).clm_apply hV).sqrt (fun t => (hVV t).ne')
  let normal : ℝ → AnnulusCoordinates := fun t => (speed t)⁻¹ • V t
  refine ⟨normal, (hsmooth.inv (fun t => (hspeed t).ne')).smul hV, ?_⟩
  intro t
  have hsq : speed t ^ 2 = N.metric.inner (gamma t) (V t) (V t) :=
    Real.sq_sqrt (hVV t).le
  refine ⟨?_, ?_, ?_⟩
  · change N.metric.inner (gamma t) ((speed t)⁻¹ • V t) ((speed t)⁻¹ • V t) = 1
    simp only [map_smul, smul_apply, smul_eq_mul, ← hsq]
    field_simp [(hspeed t).ne']
  · change N.metric.inner (gamma t) ((speed t)⁻¹ • V t)
      (curveVelocity (n := 2) gamma t) = 0
    rw [map_smul, smul_apply, smul_eq_mul, hdual, m64Intrinsic_boundary_radial_pairing,
      mul_zero]
  · change 0 < inner ℝ (gamma t) ((speed t)⁻¹ • V t)
    rw [inner_smul_right, ← hdual t (V t)]
    exact mul_pos (inv_pos.mpr (hspeed t)) (hVV t)

/-- The normal variation's initial tangential derivative is bounded below by minus the exact
absolute geodesic curvature in the public statement. Source/construction: Morgan--Tian Claim
19.37, printed pp. 468-469. -/
theorem m64Intrinsic_boundary_normal_turning_lower
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    {normal : ℝ → AnnulusCoordinates} (hnormal : ContDiff ℝ ∞ normal)
    (hunit : ∀ t, N.metric.inner (intrinsicAnnulusBoundary radius t)
      (normal t) (normal t) = 1)
    (horth : ∀ t, N.metric.inner (intrinsicAnnulusBoundary radius t) (normal t)
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) t) = 0)
    (t : ℝ) :
    -intrinsicGeodesicCurvature N.metric N.connection radius t ≤
      (intrinsicBoundarySpeed N.metric radius t)⁻¹ *
        N.metric.inner (intrinsicAnnulusBoundary radius t)
          (rampHorizontalCovariantDerivative N.connection (intrinsicAnnulusBoundary radius)
            normal t) (intrinsicBoundaryUnitTangent N.metric radius t) := by
  let gamma := intrinsicAnnulusBoundary radius
  let T := intrinsicBoundaryUnitTangent N.metric radius
  let A := rampHorizontalCovariantDerivative N.connection gamma T t
  have hgamma := m64Intrinsic_contDiff_boundary radius
  have hT := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
  have hpair : (fun s => N.metric.inner (gamma s) (normal s) (T s)) = fun _ => 0 := by
    funext s
    change N.metric.inner (gamma s) (normal s)
      ((intrinsicBoundarySpeed N.metric radius s)⁻¹ • curveVelocity (n := 2) gamma s) = 0
    rw [map_smul, smul_eq_mul, horth, mul_zero]
  have hd := M62.hasDerivAt_metric_pairing N.connection (x := t)
    ((contMDiff_iff_contDiff.mpr hgamma).mdifferentiableAt (by simp))
    (m64Intrinsic_mdifferentiable_tangent_field hgamma.contDiffAt hnormal.contDiffAt)
    (m64Intrinsic_mdifferentiable_tangent_field hgamma.contDiffAt hT.contDiffAt)
  have hz : HasDerivAt (fun s => N.metric.inner (gamma s) (normal s) (T s)) 0 t := by
    rw [hpair]
    exact hasDerivAt_const t 0
  have heq := hd.unique hz
  have hnorm : N.metric.tangentNorm (gamma t) (normal t) = 1 := by
    change Real.sqrt (N.metric.inner (gamma t) (normal t) (normal t)) = 1
    rw [hunit, Real.sqrt_one]
  have habs := m64Intrinsic_abs_metric_pairing_le N.metric (gamma t) (normal t) A
  rw [hnorm, one_mul] at habs
  have hlow : -N.metric.tangentNorm (gamma t) A ≤
      N.metric.inner (gamma t)
        (rampHorizontalCovariantDerivative N.connection gamma normal t) (T t) := by
    linarith [(abs_le.mp habs).2]
  have hturn := m64Intrinsic_turning_density N hradius t
  change intrinsicGeodesicCurvature N.metric N.connection radius t *
    intrinsicBoundarySpeed N.metric radius t = N.metric.tangentNorm (gamma t) A at hturn
  rw [← hturn] at hlow
  have hs := m64Intrinsic_boundarySpeed_pos N hradius t
  have h := mul_le_mul_of_nonneg_left hlow (inv_pos.mpr hs).le
  convert! h using 1
  field_simp

end PoincareMT
