import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Curve.PullbackContinuity
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Boundary.Geometry
import PoincareLib.Geometry.CurveShortening.Evolution.Flow

/-! Exact boundary lengths and factor-one absolute-turning transport.
Source: MT Lemma 19.31, pp. 464-466; induced-boundary-geometry derivation,
Sections 1 and 4. Every quantity uses the frozen circle and curve definitions. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle intervalIntegral

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
/-- The actual velocity of the image boundary is the differential applied to the frozen
boundary velocity. MT Lemma 19.31; derivation Section 1. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_velocity {j : AnnulusCoordinates → M} {radius x : ℝ}
    (hj : MDifferentiableAt (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x)) :
    curveVelocity (j ∘ intrinsicAnnulusBoundary radius) x =
      mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x)
        (curveVelocity (intrinsicAnnulusBoundary radius) x) := by
  have hc := ((m64Intrinsic_contDiff_boundary radius).contMDiff.mdifferentiableAt
    (by simp) (x := x))
  exact congrArg (fun L => L (1 : ℝ)) (mfderiv_comp x hj hc)

/-- Actual metric agreement preserves the pointwise speed of the image circle exactly. MT
Lemma 19.31; derivation Section 1. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466;
project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_speed (N : IntrinsicAnnulus) (g : RiemannianMetric n M)
    {j : AnnulusCoordinates → M} {radius x : ℝ}
    (hj : MDifferentiableAt (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x))
    (hmetric : ∀ u v, N.metric.inner (intrinsicAnnulusBoundary radius x) u v =
      g.inner (j (intrinsicAnnulusBoundary radius x))
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) u)
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) v)) :
    intrinsicBoundarySpeed N.metric radius x =
      g.tangentNorm (j (intrinsicAnnulusBoundary radius x))
        (curveVelocity (j ∘ intrinsicAnnulusBoundary radius) x) := by
  rw [m64_induced_boundary_velocity hj]
  exact congrArg Real.sqrt (hmetric _ _)

variable {a b : ℝ}

/-- At a fixed flow time the exact image speed is the frozen curveSpeed. Source:
Morgan--Tian Lemma 19.31, printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_curveSpeed (F : RicciFlow n M (Icc a b)) (time : ℝ)
    (N : IntrinsicAnnulus) {j : AnnulusCoordinates → M} {radius x : ℝ}
    (hj : MDifferentiableAt (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x))
    (hmetric : ∀ u v, N.metric.inner (intrinsicAnnulusBoundary radius x) u v =
      (F.metric time).inner (j (intrinsicAnnulusBoundary radius x))
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) u)
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) v)) :
    intrinsicBoundarySpeed N.metric radius x =
      curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x :=
  m64_induced_boundary_speed N (F.metric time) hj hmetric

/-- The intrinsic circle length is the literal length integral of its image at the fixed
flow time, on every parameter interval. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_length (F : RicciFlow n M (Icc a b)) (time : ℝ)
    (N : IntrinsicAnnulus) {j : AnnulusCoordinates → M} {radius : ℝ}
    (hj : ∀ x, MDifferentiableAt (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x))
    (hmetric : ∀ x u v, N.metric.inner (intrinsicAnnulusBoundary radius x) u v =
      (F.metric time).inner (j (intrinsicAnnulusBoundary radius x))
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) u)
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) v))
    (alpha beta : ℝ) :
    intrinsicBoundaryLength N.metric radius alpha beta =
      ∫ x in alpha..beta,
        curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x := by
  apply intervalIntegral.integral_congr
  intro x _hx
  exact m64_induced_boundary_curveSpeed F time N (hj x) (hmetric x)

/-- Over one full period the exact image length is the frozen m62Length. Source:
Morgan--Tian Lemma 19.31, printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_m62Length (F : RicciFlow n M (Icc a b)) (time : ℝ)
    (N : IntrinsicAnnulus) {j : AnnulusCoordinates → M} {radius : ℝ}
    (hj : ∀ x, MDifferentiableAt (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x))
    (hmetric : ∀ x u v, N.metric.inner (intrinsicAnnulusBoundary radius x) u v =
      (F.metric time).inner (j (intrinsicAnnulusBoundary radius x))
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) u)
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) v)) :
    intrinsicBoundaryLength N.metric radius 0 curvePeriod =
      m62Length F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time :=
  m64_induced_boundary_length F time N hj hmetric 0 curvePeriod

private theorem tangentNorm_smul (g : RiemannianMetric n M) (p : M)
    (r : ℝ) (v : TangentSpace (𝓡 n) p) :
    g.tangentNorm p (r • v) = |r| * g.tangentNorm p v := by
  simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [show r * (r * g.inner p v v) = r ^ 2 * g.inner p v v by ring,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

/-- The actual absolute-curvature density is the norm of the parameter derivative of the
unit tangent whenever the actual speed is positive. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_curve_turning_density (F : RicciFlow n M (Icc a b))
    (c : ℝ → ℝ → M) (time x : ℝ) (hs : 0 < curveSpeed F c time x) :
    m62Curvature F c time x * curveSpeed F c time x =
      (F.metric time).tangentNorm (c x time)
        (rampHorizontalCovariantDerivative (F.connection time) (fun y => c y time)
          (spatialUnitTangent F c time) x) := by
  change (F.metric time).tangentNorm (c x time)
      ((curveSpeed F c time x)⁻¹ •
        rampHorizontalCovariantDerivative (F.connection time) (fun y => c y time)
          (spatialUnitTangent F c time) x) * curveSpeed F c time x = _
  rw [tangentNorm_smul, abs_of_pos (inv_pos.mpr hs)]
  field_simp

/-- The actual ambient unit tangent is the image of the intrinsic one; the two curves retain
exactly the same parameter. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466; project
derivation `proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_unitTangent (F : RicciFlow n M (Icc a b)) (time : ℝ)
    (N : IntrinsicAnnulus) {j : AnnulusCoordinates → M} {radius : ℝ}
    (hj : ∀ x, MDifferentiableAt (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x))
    (hmetric : ∀ x u v, N.metric.inner (intrinsicAnnulusBoundary radius x) u v =
      (F.metric time).inner (j (intrinsicAnnulusBoundary radius x))
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) u)
        (mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x) v)) :
    spatialUnitTangent F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time =
      fun x => mfderiv (𝓡 2) (𝓡 n) j (intrinsicAnnulusBoundary radius x)
        (intrinsicBoundaryUnitTangent N.metric radius x) := by
  funext x
  have hs := m64_induced_boundary_curveSpeed F time N (hj x) (hmetric x)
  change _⁻¹ • curveVelocity (j ∘ intrinsicAnnulusBoundary radius) x = _
  rw [← hs, m64_induced_boundary_velocity (hj x), intrinsicBoundaryUnitTangent, map_smul]

/-- Absolute-turning density decreases under the actual tangential projection, with constant
one. MT Lemma 19.31; derivation Section 4. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_turning_density_le
    (F : RicciFlow n M (Icc a b)) (time : ℝ) (N : IntrinsicAnnulus)
    {j : AnnulusCoordinates → M} {radius : ℝ} (hradius : radius ≠ 0)
    (hj : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x),
      ContMDiffAt (𝓡 2) (𝓡 n) ∞ j q)
    (hmetric : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x), ∀ u v,
      N.metric.inner q u v = (F.metric time).inner (j q)
        (mfderiv (𝓡 2) (𝓡 n) j q u) (mfderiv (𝓡 2) (𝓡 n) j q v)) (x : ℝ) :
    intrinsicGeodesicCurvature N.metric N.connection radius x *
        intrinsicBoundarySpeed N.metric radius x ≤
      m62Curvature F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x *
        curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x := by
  have hj' := fun y => (hj y).self_of_nhds.mdifferentiableAt (by simp)
  have hmetric' := fun y => (hmetric y).self_of_nhds
  have hs := m64_induced_boundary_curveSpeed F time N (hj' x) (hmetric' x)
  have hpos : 0 < curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x := by
    rw [← hs]
    exact m64Intrinsic_boundarySpeed_pos N hradius x
  have hunit := m64_induced_boundary_unitTangent F time N hj' hmetric'
  rw [m64Intrinsic_turning_density N hradius,
    m64_curve_turning_density F _ time x hpos, hunit]
  exact m64_induced_manifold_curve_connection_norm_le (F.connection time) N.connection
    (hj x) ((m64Intrinsic_contDiff_boundary radius).contDiffAt.of_le (by norm_cast))
    ((m64Intrinsic_contDiff_boundaryUnitTangent N hradius).contDiffAt.of_le (by norm_cast))
    (hmetric x)

/-- The intrinsic absolute geodesic curvature is bounded by the actual ambient m62
curvature, with no multiplicative loss. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_curvature_le
    (F : RicciFlow n M (Icc a b)) (time : ℝ) (N : IntrinsicAnnulus)
    {j : AnnulusCoordinates → M} {radius : ℝ} (hradius : radius ≠ 0)
    (hj : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x),
      ContMDiffAt (𝓡 2) (𝓡 n) ∞ j q)
    (hmetric : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x), ∀ u v,
      N.metric.inner q u v = (F.metric time).inner (j q)
        (mfderiv (𝓡 2) (𝓡 n) j q u) (mfderiv (𝓡 2) (𝓡 n) j q v)) (x : ℝ) :
    intrinsicGeodesicCurvature N.metric N.connection radius x ≤
      m62Curvature F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x := by
  have hle := m64_induced_boundary_turning_density_le F time N hradius hj hmetric x
  have hs := m64_induced_boundary_curveSpeed F time N
    ((hj x).self_of_nhds.mdifferentiableAt (by simp)) (hmetric x).self_of_nhds
  rw [← hs] at hle
  exact le_of_mul_le_mul_right hle (m64Intrinsic_boundarySpeed_pos N hradius x)

/-- The actual ambient absolute-turning density of the image boundary is continuous, so its
compact-interval integrability is a conclusion. Source: Morgan--Tian Lemma 19.31, printed
pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_turning_continuous
    (F : RicciFlow n M (Icc a b)) (time : ℝ) (N : IntrinsicAnnulus)
    {j : AnnulusCoordinates → M} {radius : ℝ} (hradius : radius ≠ 0)
    (hj : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x),
      ContMDiffAt (𝓡 2) (𝓡 n) ∞ j q)
    (hmetric : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x), ∀ u v,
      N.metric.inner q u v = (F.metric time).inner (j q)
        (mfderiv (𝓡 2) (𝓡 n) j q u) (mfderiv (𝓡 2) (𝓡 n) j q v)) :
    Continuous (fun x =>
      m62Curvature F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x *
        curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x) := by
  have hj' := fun y => (hj y).self_of_nhds.mdifferentiableAt (by simp)
  have hmetric' := fun y => (hmetric y).self_of_nhds
  have hunit := m64_induced_boundary_unitTangent F time N hj' hmetric'
  have hcont := m64_pushforward_pullback_norm_continuous (F.connection time) hj
    (m64Intrinsic_contDiff_boundary radius)
    (m64Intrinsic_contDiff_boundaryUnitTangent N hradius)
  apply hcont.congr
  intro x
  have hs := m64_induced_boundary_curveSpeed F time N (hj' x) (hmetric' x)
  have hpos : 0 < curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x := by
    rw [← hs]
    exact m64Intrinsic_boundarySpeed_pos N hradius x
  rw [m64_curve_turning_density F _ time x hpos, hunit]
  rfl

/-- Integrating the actual factor-one projection gives the intrinsic absolute-turning bound
on every ordered parameter interval. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466;
project derivation
`proof-work/tasks/M64/derivations/2026-09-27-induced-boundary-geometry.md`. -/
theorem m64_induced_boundary_turning_integral_le
    (F : RicciFlow n M (Icc a b)) (time : ℝ) (N : IntrinsicAnnulus)
    {j : AnnulusCoordinates → M} {radius : ℝ} (hradius : radius ≠ 0)
    (hj : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x),
      ContMDiffAt (𝓡 2) (𝓡 n) ∞ j q)
    (hmetric : ∀ x, ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x), ∀ u v,
      N.metric.inner q u v = (F.metric time).inner (j q)
        (mfderiv (𝓡 2) (𝓡 n) j q u) (mfderiv (𝓡 2) (𝓡 n) j q v))
    {alpha beta : ℝ} (hab : alpha ≤ beta) :
    intrinsicGeodesicCurvatureIntegral N.metric N.connection radius alpha beta ≤
      ∫ x in alpha..beta,
        m62Curvature F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x *
          curveSpeed F (fun y _ => j (intrinsicAnnulusBoundary radius y)) time x := by
  exact intervalIntegral.integral_mono_on hab
    ((m64Intrinsic_continuous_turning_density N hradius).intervalIntegrable alpha beta)
    ((m64_induced_boundary_turning_continuous F time N hradius hj hmetric).intervalIntegrable
      alpha beta)
    (fun x _hx => m64_induced_boundary_turning_density_le F time N hradius hj hmetric x)

end PoincareMT
