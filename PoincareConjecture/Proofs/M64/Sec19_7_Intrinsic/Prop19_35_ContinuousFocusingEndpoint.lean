import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingEndpoint

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_focusing_endpoint_le_absoluteTurning_of_continuousOn
    (N : IntrinsicAnnulus) {radius a b C S : ℝ} (hradius : radius ≠ 0)
    (hab : a ≤ b) {Y : ℝ → AnnulusCoordinates}
    (hYc : ContinuousOn Y (Icc a b))
    (hY : ∀ x ∈ Ioo a b, ContDiffAt ℝ ∞ Y x)
    (hfocus : ∀ x ∈ Ioo a b,
      C * intrinsicBoundarySpeed N.metric radius x ≤
        N.metric.inner (intrinsicAnnulusBoundary radius x)
          (rampHorizontalCovariantDerivative N.connection (intrinsicAnnulusBoundary radius) Y x)
          (intrinsicBoundaryUnitTangent N.metric radius x))
    (hbound : ∀ x ∈ Ioo a b,
      N.metric.tangentNorm (intrinsicAnnulusBoundary radius x) (Y x) ≤ S)
    (ha : N.metric.inner (intrinsicAnnulusBoundary radius a) (Y a)
      (intrinsicBoundaryUnitTangent N.metric radius a) = 0)
    (hb : N.metric.inner (intrinsicAnnulusBoundary radius b) (Y b)
      (intrinsicBoundaryUnitTangent N.metric radius b) = 0) :
    C * intrinsicBoundaryLength N.metric radius a b ≤
      S * intrinsicGeodesicCurvatureIntegral N.metric N.connection radius a b := by
  let gamma := intrinsicAnnulusBoundary radius
  let T := intrinsicBoundaryUnitTangent N.metric radius
  let f : ℝ → ℝ := fun x => N.metric.inner (gamma x) (Y x) (T x)
  let df : ℝ → ℝ := fun x => N.metric.inner (gamma x)
    (rampHorizontalCovariantDerivative N.connection gamma Y x) (T x) +
      N.metric.inner (gamma x) (Y x)
        (rampHorizontalCovariantDerivative N.connection gamma T x)
  let phi : ℝ → ℝ := fun x => C * intrinsicBoundarySpeed N.metric radius x -
    S * (intrinsicGeodesicCurvature N.metric N.connection radius x *
      intrinsicBoundarySpeed N.metric radius x)
  have hgamma := m64Intrinsic_contDiff_boundary radius
  have hT := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
  have hg : ContDiff ℝ ∞ N.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr N.metric.contDiffAt_euclideanCoefficients
  have hcont : ContinuousOn f (Icc a b) :=
    (((hg.comp hgamma).continuous.continuousOn.clm_apply hYc).clm_apply
      hT.continuous.continuousOn)
  have hderiv (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt f (df x) x := by
    exact M62.hasDerivAt_metric_pairing N.connection
      ((contMDiff_iff_contDiff.mpr hgamma).mdifferentiableAt (by simp))
      (m64Intrinsic_mdifferentiable_tangent_field hgamma.contDiffAt (hY x hx))
      (m64Intrinsic_mdifferentiable_tangent_field hgamma.contDiffAt hT.contDiffAt)
  have hphic : Continuous phi :=
    ((m64Intrinsic_contDiff_boundarySpeed N hradius).continuous.const_mul C).sub
      ((m64Intrinsic_continuous_turning_density N hradius).const_mul S)
  have hphidf (x : ℝ) (hx : x ∈ Ioo a b) : phi x ≤ df x := by
    let A := rampHorizontalCovariantDerivative N.connection gamma T x
    have hA : 0 ≤ N.metric.tangentNorm (gamma x) A := Real.sqrt_nonneg _
    have habs := (m64Intrinsic_abs_metric_pairing_le N.metric (gamma x) (Y x) A).trans
      (mul_le_mul_of_nonneg_right (hbound x hx) hA)
    have hneg := (abs_le.mp habs).1
    have ht := m64Intrinsic_turning_density N hradius x
    change intrinsicGeodesicCurvature N.metric N.connection radius x *
      intrinsicBoundarySpeed N.metric radius x = N.metric.tangentNorm (gamma x) A at ht
    dsimp only [phi, df]
    rw [ht]
    have hfoc := hfocus x hx
    change C * intrinsicBoundarySpeed N.metric radius x ≤
      N.metric.inner (gamma x)
        (rampHorizontalCovariantDerivative N.connection gamma Y x) (T x) at hfoc
    linarith
  have hint := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hcont
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hphic.integrableOn_Icc hphidf
  change (∫ x in a..b, phi x) ≤
    N.metric.inner (intrinsicAnnulusBoundary radius b) (Y b)
        (intrinsicBoundaryUnitTangent N.metric radius b) -
      N.metric.inner (intrinsicAnnulusBoundary radius a) (Y a)
        (intrinsicBoundaryUnitTangent N.metric radius a) at hint
  rw [ha, hb, sub_self] at hint
  dsimp only [phi] at hint
  have hspeedC := (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous.const_mul C
  have hspeedI := hspeedC.intervalIntegrable (μ := volume) a b
  have hturnC := (m64Intrinsic_continuous_turning_density N hradius).const_mul S
  have hturnI := hturnC.intervalIntegrable (μ := volume) a b
  rw [intervalIntegral.integral_sub hspeedI hturnI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  exact sub_nonpos.mp hint

end PoincareConjecture
