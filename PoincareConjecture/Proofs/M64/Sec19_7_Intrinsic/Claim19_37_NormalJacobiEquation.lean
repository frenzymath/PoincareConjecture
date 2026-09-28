import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalRegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Coordinates









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem m64Intrinsic_phase_time_partial
    (N : IntrinsicAnnulus)
    {phase : ℝ × ℝ → AnnulusCoordinates × AnnulusCoordinates} {z : ℝ × ℝ}
    (hsmooth : DifferentiableAt ℝ phase z)
    (hode : HasDerivAt (fun t => phase (z.1, t))
      (coordinateGeodesicField N.metric.euclideanCoefficients (phase z)) z.2) :
    fderiv ℝ (fun p => (phase p).1) z (0, 1) = (phase z).2 ∧
      fderiv ℝ (fun p => (phase p).2) z (0, 1) =
        -coordinateChristoffel N.metric.euclideanCoefficients
          (phase z).1 (phase z).2 (phase z).2 := by
  have hfirst := hsmooth.fst.hasFDerivAt.comp_hasDerivAt
    (l := fun p => (phase p).1) (f := fun t => (z.1, t)) z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have hsecond := hsmooth.snd.hasFDerivAt.comp_hasDerivAt
    (l := fun p => (phase p).2) (f := fun t => (z.1, t)) z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have hposition : HasDerivAt (fun t => (phase (z.1, t)).1) (phase z).2 z.2 := by
    simpa [coordinateGeodesicField] using hode.hasFDerivAt.fst.hasDerivAt
  have hvelocity : HasDerivAt (fun t => (phase (z.1, t)).2)
      (-coordinateChristoffel N.metric.euclideanCoefficients
        (phase z).1 (phase z).2 (phase z).2) z.2 := by
    simpa [coordinateGeodesicField] using hode.hasFDerivAt.snd.hasDerivAt
  exact ⟨hfirst.unique hposition, hsecond.unique hvelocity⟩




theorem m64Intrinsic_normal_variation_jacobi
    (N : IntrinsicAnnulus)
    {phase : ℝ × ℝ → AnnulusCoordinates × AnnulusCoordinates}
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hsmooth : ContDiffOn ℝ ∞ phase Omega)
    (hode : ∀ z ∈ Omega, HasDerivAt (fun t => phase (z.1, t))
      (coordinateGeodesicField N.metric.euclideanCoefficients (phase z)) z.2)
    {z : ℝ × ℝ} (hz : z ∈ Omega) :
    let F : ℝ × ℝ → AnnulusCoordinates := fun p => (phase p).1
    let Gamma := christoffelBilinear N.metric.euclideanCoefficients
    let X : ℝ × ℝ → AnnulusCoordinates := fun p => fderiv ℝ F p (1, 0)
    covDerivAlong Gamma F (covDerivAlong Gamma F X (0, 1)) (0, 1) z +
      christoffelCurvature Gamma (F z) (X z) (phase z).2 (phase z).2 = 0 := by
  let F : ℝ × ℝ → AnnulusCoordinates := fun p => (phase p).1
  let V : ℝ × ℝ → AnnulusCoordinates := fun p => (phase p).2
  let Gamma := christoffelBilinear N.metric.euclideanCoefficients
  have hF : ContDiffOn ℝ ∞ F Omega := hsmooth.fst
  have hpartial (p : ℝ × ℝ) (hp : p ∈ Omega) :=
    m64Intrinsic_phase_time_partial N
      ((hsmooth.contDiffAt (hOmega.mem_nhds hp)).differentiableAt (by simp)) (hode p hp)
  have haccel (p : ℝ × ℝ) (hp : p ∈ Omega) :
      covDerivAlong Gamma F (fun q => fderiv ℝ F q (0, 1)) (0, 1) p = 0 := by
    have hVeq : (fun q => fderiv ℝ F q (0, 1)) =ᶠ[𝓝 p] V := by
      filter_upwards [hOmega.mem_nhds hp] with q hq
      exact (hpartial q hq).1
    rw [covDerivAlong_congr Gamma F hVeq, covDerivAlong]
    change fderiv ℝ V p (0, 1) +
      coordinateChristoffel N.metric.euclideanCoefficients (F p)
        (fderiv ℝ F p (0, 1)) (V p) = 0
    rw [(hpartial p hp).1, (hpartial p hp).2]
    exact neg_add_cancel _
  have hGamma : DifferentiableAt ℝ Gamma (F z) :=
    (contDiffAt_christoffelBilinear (N.metric.contDiffAt_euclideanCoefficients (F z))
      (N.metric.inner_isInvertible (F z))).differentiableAt (by simp)
  have hsymm : ∀ᶠ p in 𝓝 z, ∀ v w, Gamma (F p) v w = Gamma (F p) w v := by
    apply Eventually.of_forall
    intro p v w
    exact christoffelBilinear_symm
      ((N.metric.contDiffAt_euclideanCoefficients (F p)).differentiableAt (by simp))
      (Eventually.of_forall fun q x y => N.metric.symm q x y) v w
  have hgeo : ∀ᶠ p in 𝓝 z,
      covDerivAlong Gamma F (fun q => fderiv ℝ F q (0, 1)) (0, 1) p = 0 := by
    filter_upwards [hOmega.mem_nhds hz] with p hp
    exact haccel p hp
  have h := covDerivAlong_geodesic_family_jacobi (ds := (1, 0)) (dt := (0, 1))
    ((hF.contDiffAt (hOmega.mem_nhds hz)).of_le
      (WithTop.coe_le_coe.2 (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))) hGamma hsymm hgeo
  rw [(hpartial z hz).1] at h
  exact h




theorem m64Intrinsic_christoffel_curvature_pairing
    (N : IntrinsicAnnulus) (p X T W : AnnulusCoordinates) :
    N.metric.inner p
      (christoffelCurvature (christoffelBilinear N.metric.euclideanCoefficients) p X T T) W =
      N.connection.scalarCurvature p / 2 *
        (N.metric.inner p X W * N.metric.inner p T T -
          N.metric.inner p X T * N.metric.inner p T W) := by
  have hGamma : DifferentiableAt ℝ (christoffelBilinear N.metric.euclideanCoefficients) p :=
    (contDiffAt_christoffelBilinear (N.metric.contDiffAt_euclideanCoefficients p)
      (N.metric.inner_isInvertible p)).differentiableAt (by simp)
  rw [← coordinateCurvature_eq_christoffelCurvature hGamma X T T,
    coordinateCurvature_eq_retained N.connection]
  change N.connection.curvatureTensor p X T W T = _
  exact N.connection.curvatureTensor_eq_half_scalarCurvature p X T W T




theorem m64Intrinsic_normal_variation_gaussian_jacobi
    (N : IntrinsicAnnulus)
    {phase : ℝ × ℝ → AnnulusCoordinates × AnnulusCoordinates}
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hsmooth : ContDiffOn ℝ ∞ phase Omega)
    (hode : ∀ z ∈ Omega, HasDerivAt (fun t => phase (z.1, t))
      (coordinateGeodesicField N.metric.euclideanCoefficients (phase z)) z.2)
    {z : ℝ × ℝ} (hz : z ∈ Omega) (W : AnnulusCoordinates) :
    let F : ℝ × ℝ → AnnulusCoordinates := fun p => (phase p).1
    let Gamma := christoffelBilinear N.metric.euclideanCoefficients
    let X : ℝ × ℝ → AnnulusCoordinates := fun p => fderiv ℝ F p (1, 0)
    N.metric.inner (F z)
        (covDerivAlong Gamma F (covDerivAlong Gamma F X (0, 1)) (0, 1) z) W +
      N.connection.scalarCurvature (F z) / 2 *
        (N.metric.inner (F z) (X z) W * N.metric.inner (F z) (phase z).2 (phase z).2 -
          N.metric.inner (F z) (X z) (phase z).2 * N.metric.inner (F z) (phase z).2 W) = 0 := by
  have h := congrArg (fun v => N.metric.inner (phase z).1 v W)
    (m64Intrinsic_normal_variation_jacobi N hOmega hsmooth hode hz)
  simp only [map_add, add_apply, map_zero, zero_apply] at h
  rw [m64Intrinsic_christoffel_curvature_pairing N] at h
  exact h

end PoincareConjecture
