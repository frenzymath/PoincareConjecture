import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_mdifferentiable_tangent_field
    {γ Y : ℝ → AnnulusCoordinates} {x : ℝ}
    (hγ : ContDiffAt ℝ ∞ γ x) (hY : ContDiffAt ℝ ∞ Y x) :
    MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 2).prod (𝓡 2))
      (fun s => (⟨γ s, Y s⟩ : TangentBundle (𝓡 2) AnnulusCoordinates)) x := by
  apply ContMDiffAt.mdifferentiableAt (n := ∞) _ (by simp)
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_iff_contDiffAt.mpr hγ, ?_⟩
  simpa only [trivializationAt_model_space_apply] using
    (contMDiffAt_iff_contDiffAt.mpr hY)

theorem m64Intrinsic_focusing_endpoint_le_absoluteTurning
    (N : IntrinsicAnnulus) {radius a b C S : ℝ} (hradius : radius ≠ 0)
    (hab : a ≤ b) {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    {Y : ℝ → AnnulusCoordinates} (hY : ContDiffOn ℝ ∞ Y U)
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
  let γ := intrinsicAnnulusBoundary radius
  let T := intrinsicBoundaryUnitTangent N.metric radius
  let f : ℝ → ℝ := fun x => N.metric.inner (γ x) (Y x) (T x)
  let df : ℝ → ℝ := fun x => N.metric.inner (γ x)
    (rampHorizontalCovariantDerivative N.connection γ Y x) (T x) +
      N.metric.inner (γ x) (Y x) (rampHorizontalCovariantDerivative N.connection γ T x)
  let φ : ℝ → ℝ := fun x => C * intrinsicBoundarySpeed N.metric radius x -
    S * (intrinsicGeodesicCurvature N.metric N.connection radius x *
      intrinsicBoundarySpeed N.metric radius x)
  have hγ := m64Intrinsic_contDiff_boundary radius
  have hT := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
  have hderiv (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt f (df x) x := by
    exact M62.hasDerivAt_metric_pairing N.connection
      ((contMDiff_iff_contDiff.mpr hγ).mdifferentiableAt (by simp))
      (m64Intrinsic_mdifferentiable_tangent_field hγ.contDiffAt
        (hY.contDiffAt (hU.mem_nhds (hsub hx))))
      (m64Intrinsic_mdifferentiable_tangent_field hγ.contDiffAt hT.contDiffAt)
  have hcont : ContinuousOn f (Icc a b) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hφc : Continuous φ :=
    ((m64Intrinsic_contDiff_boundarySpeed N hradius).continuous.const_mul C).sub
      ((m64Intrinsic_continuous_turning_density N hradius).const_mul S)
  have hφdf (x : ℝ) (hx : x ∈ Ioo a b) : φ x ≤ df x := by
    let A := rampHorizontalCovariantDerivative N.connection γ T x
    have hA : 0 ≤ N.metric.tangentNorm (γ x) A := Real.sqrt_nonneg _
    have habs := (m64Intrinsic_abs_metric_pairing_le N.metric (γ x) (Y x) A).trans
      (mul_le_mul_of_nonneg_right (hbound x hx) hA)
    have hneg := (abs_le.mp habs).1
    have ht := m64Intrinsic_turning_density N hradius x
    change intrinsicGeodesicCurvature N.metric N.connection radius x *
      intrinsicBoundarySpeed N.metric radius x = N.metric.tangentNorm (γ x) A at ht
    dsimp only [φ, df]
    rw [ht]
    have hfoc := hfocus x hx
    change C * intrinsicBoundarySpeed N.metric radius x ≤
      N.metric.inner (γ x) (rampHorizontalCovariantDerivative N.connection γ Y x) (T x)
      at hfoc
    linarith
  have hint := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hcont
    (fun x hx => (hderiv x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt)
    hφc.integrableOn_Icc hφdf
  change (∫ x in a..b, φ x) ≤
    N.metric.inner (intrinsicAnnulusBoundary radius b) (Y b)
      (intrinsicBoundaryUnitTangent N.metric radius b) -
    N.metric.inner (intrinsicAnnulusBoundary radius a) (Y a)
      (intrinsicBoundaryUnitTangent N.metric radius a) at hint
  rw [ha, hb, sub_self] at hint
  dsimp only [φ] at hint
  have hspeedC := (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous.const_mul C
  have hspeedI := hspeedC.intervalIntegrable (μ := volume) a b
  have hturnC := (m64Intrinsic_continuous_turning_density N hradius).const_mul S
  have hturnI := hturnC.intervalIntegrable (μ := volume) a b
  rw [intervalIntegral.integral_sub hspeedI hturnI,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  exact sub_nonpos.mp hint

end PoincareConjecture
