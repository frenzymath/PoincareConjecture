import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Normal.Scalar
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Focusing.Transport

/-!
# The initial derivative of the normal Jacobi coefficient

The coordinate, intrinsic, and frozen pullback connections coincide on the
intrinsic plane. Torsion-freeness of the actual two-parameter pullback then
identifies the time derivative of the variation field with the boundary
derivative of the normal. Source: Claim 19.37, pp. 468-469.

Context: Morgan--Tian Claim 19.37, printed pp. 468-469, in the proof of Proposition
19.35.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT

open ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The chart-based intrinsic derivative has the global Euclidean Christoffel formula on the
intrinsic surface. Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_manifoldCovDeriv_model
    (N : IntrinsicAnnulus) (q V : ℝ → AnnulusCoordinates) (t : ℝ) :
    manifoldCovDerivAlong N.metric q V 1 t =
      deriv V t + coordinateChristoffel N.metric.euclideanCoefficients (q t)
        (deriv q t) (V t) := by
  have hcoeff : N.metric.pullbackCoefficients id = N.metric.euclideanCoefficients := by
    ext p v w
    change N.metric.inner p (mfderiv (𝓡 2) (𝓡 2) id p v)
      (mfderiv (𝓡 2) (𝓡 2) id p w) = N.metric.inner p v w
    rw [mfderiv_id]
    rfl
  simp [manifoldCovDerivAlong, hcoeff, covDerivAlong, fderiv_eq_smul_deriv]

/-- The M07 chart-defined and M62 frozen derivatives agree for smooth fields along the
actual intrinsic curve. Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_manifoldCovDeriv_eq_frozen
    (N : IntrinsicAnnulus) {q V : ℝ → AnnulusCoordinates} {I : Set ℝ}
    (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) (hq : DifferentiableAt ℝ q t)
    (hV : ContDiffOn ℝ ∞ V I) :
    manifoldCovDerivAlong N.metric q V 1 t =
      rampHorizontalCovariantDerivative N.connection q V t := by
  exact (m64Intrinsic_manifoldCovDeriv_model N q V t).trans
    (m64Intrinsic_pullback_modelOn N hI ht hq hV).symm

/-- Torsion-freeness computes the initial covariant derivative of the normal variation field
from the actual boundary normal derivative. Source/construction: Morgan--Tian Claim 19.37,
printed pp. 468-469. -/
theorem m64Intrinsic_normal_variation_initial_covDeriv
    (N : IntrinsicAnnulus) {radius : ℝ}
    {u : ℝ × ℝ → AnnulusCoordinates} {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I))
    (hboundary : ∀ s ∈ S, u (s, 0) = intrinsicAnnulusBoundary radius s)
    {normal : ℝ → AnnulusCoordinates} (hnormal : ContDiff ℝ ∞ normal)
    (hvelocity : ∀ s ∈ S, curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s)
    {a : ℝ} (ha : a ∈ S) :
    let q : ℝ → AnnulusCoordinates := fun t => u (a, t)
    let X : ℝ → AnnulusCoordinates := fun t => curveVelocity (n := 2) (fun s => u (s, t)) a
    manifoldCovDerivAlong N.metric q X 1 0 =
      rampHorizontalCovariantDerivative N.connection
        (intrinsicAnnulusBoundary radius) normal a := by
  let q : ℝ → AnnulusCoordinates := fun t => u (a, t)
  let X : ℝ → AnnulusCoordinates :=
    fun t => curveVelocity (n := 2) (fun s => u (s, t)) a
  let base : ℝ → AnnulusCoordinates := fun s => u (s, 0)
  let V : ℝ → AnnulusCoordinates := fun s => curveVelocity (n := 2) (fun t => u (s, t)) 0
  have huat := hu.contMDiffAt ((hS.prod hI).mem_nhds
    (show (a, 0) ∈ S ×ˢ I from ⟨ha, hzero⟩))
  have hq : DifferentiableAt ℝ q 0 :=
    ((contMDiffAt_iff_contDiffAt.mp huat).comp 0 (by fun_prop)).differentiableAt (by simp)
  have hbase : DifferentiableAt ℝ base a :=
    ((contMDiffAt_iff_contDiffAt.mp huat).comp a (by fun_prop)).differentiableAt (by simp)
  have hX : ContDiffOn ℝ ∞ X I := fun t ht =>
    (m64Intrinsic_contDiff_variation_field hS hI hu.contDiffOn ha ht).contDiffWithinAt
  have hge : base =ᶠ[𝓝 a] intrinsicAnnulusBoundary radius := by
    filter_upwards [hS.mem_nhds ha] with s hs
    exact hboundary s hs
  have hveq : V =ᶠ[𝓝 a] normal := by
    filter_upwards [hS.mem_nhds ha] with s hs
    exact hvelocity s hs
  have hcomm := M62.pullback_velocity_commute N.connection (fun s t => u (s, t))
    (hS.prod hI) hu (show (a, 0) ∈ S ×ˢ I from ⟨ha, hzero⟩)
  change rampHorizontalCovariantDerivative N.connection q X 0 =
    rampHorizontalCovariantDerivative N.connection base V a at hcomm
  have hright : rampHorizontalCovariantDerivative N.connection base V a =
      rampHorizontalCovariantDerivative N.connection
        (intrinsicAnnulusBoundary radius) normal a := by
    exact (M62.pullback_congr N.connection hveq).trans
      (m64Intrinsic_pullback_congr_base N hS ha hbase
        ((m64Intrinsic_contDiff_boundary radius).contDiffAt.differentiableAt (by simp))
        hnormal.contDiffOn hge)
  exact (m64Intrinsic_manifoldCovDeriv_eq_frozen N hI hzero hq hX).trans
    (hcomm.trans hright)

end PoincareMT
