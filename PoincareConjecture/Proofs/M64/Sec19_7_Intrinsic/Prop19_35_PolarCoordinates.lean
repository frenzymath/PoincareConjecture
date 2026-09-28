import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RayComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

open RiemannianMetric

theorem m64Intrinsic_ricci_lower_at_of_curvature_norm
    (N : IntrinsicAnnulus) (K : ℝ)
    (p : AnnulusCoordinates)
    (hcurv : N.connection.curvatureTensorNorm p ≤ K)
    (v : TangentSpace (𝓡 2) p) :
    -((1 : ℝ) * K) * N.metric.inner p v v ≤
      N.connection.ricci p v v := by
  have hsec : ∀ u w : TangentSpace (𝓡 2) p,
      |N.connection.sectionalCurvature p u w| ≤ K := by
    intro u w
    exact (N.connection.abs_sectionalCurvature_le_curvatureTensorNorm p u w).trans hcurv
  have h := N.connection.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le
    p K hsec v
  norm_num at h
  simpa only [Nat.cast_one, one_mul, neg_mul] using h

theorem m64Intrinsic_ricci_lower_of_curvature_norm
    (N : IntrinsicAnnulus) (K : ℝ)
    (hcurv : ∀ p ∈ standardAnnulusDomain,
      N.connection.curvatureTensorNorm p ≤ K)
    (p : AnnulusCoordinates) (hp : p ∈ standardAnnulusDomain)
    (v : TangentSpace (𝓡 2) p) :
    -((1 : ℝ) * K) * N.metric.inner p v v ≤
      N.connection.ricci p v v := by
  exact m64Intrinsic_ricci_lower_at_of_curvature_norm N K p (hcurv p hp) v

theorem m64Intrinsic_radial_ricci_lower_of_ball_curvature_norm
    (N : IntrinsicAnnulus) (K R : ℝ)
    (p : AnnulusCoordinates)
    (hcurv : ∀ q ∈ N.metric.ball p R,
      N.connection.curvatureTensorNorm q ≤ K)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {theta : AnnulusCoordinates} {b : ℝ}
    (hmap : ∀ s ∈ Ioo (0 : ℝ) b,
      e (s • theta) ∈ N.metric.ball p R) :
    ∀ s ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (s • theta)),
        -((1 : ℕ) : ℝ) * K * N.metric.inner (e (s • theta)) w w ≤
          N.connection.ricci (e (s • theta)) w w := by
  intro s hs w
  have hpoint := m64Intrinsic_ricci_lower_at_of_curvature_norm N K
    (e (s • theta)) (hcurv (e (s • theta)) (hmap s hs)) w
  simpa only [Nat.cast_one, one_mul, neg_mul] using hpoint

theorem m64Intrinsic_radial_ricci_lower_of_curvature_norm
    (N : IntrinsicAnnulus) (K : ℝ)
    (hcurv : ∀ p ∈ standardAnnulusDomain,
      N.connection.curvatureTensorNorm p ≤ K)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {theta : AnnulusCoordinates} {b : ℝ}
    (hmap : ∀ s ∈ Ioo (0 : ℝ) b,
      e (s • theta) ∈ standardAnnulusDomain) :
    ∀ s ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (s • theta)),
        -((1 : ℕ) : ℝ) * K * N.metric.inner (e (s • theta)) w w ≤
          N.connection.ricci (e (s • theta)) w w := by
  intro s hs w
  have h := m64Intrinsic_ricci_lower_of_curvature_norm N K hcurv
    (e (s • theta)) (hmap s hs) w
  simpa only [Nat.cast_one, one_mul, neg_mul] using h

theorem m64Intrinsic_polarDensity_cross_le_of_ricci
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U, RiemannianMetric.IsGeodesicOn N.metric
      (fun s : ℝ => e (s • v))
      {s : ℝ | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0)
        (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b kappa : ℝ} (hb : 0 < b) (hkappa : 0 ≤ kappa)
    (hsub : ∀ s ∈ Icc (0 : ℝ) b, s • theta ∈ U)
    (hinj : ∀ s ∈ Icc (0 : ℝ) b,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (s • theta)))
    (hRic : ∀ s ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (s • theta)),
        -(1 : ℝ) * kappa * N.metric.inner (e (s • theta)) w w ≤
          N.connection.ricci (e (s • theta)) w w)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) b)
    (hs : s ∈ Ioo (0 : ℝ) b) (hts : t ≤ s) :
    (s ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (s • theta)) *
        modelS kappa t ^ (1 : ℕ) ≤
      (t ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (t • theta)) *
        modelS kappa s ^ (1 : ℕ) := by
  have hRic' : ∀ u ∈ Ioo (0 : ℝ) b,
      ∀ w : TangentSpace (𝓡 (1 + 1)) (e (u • theta)),
        -((1 : ℕ) : ℝ) * kappa * N.metric.inner (e (u • theta)) w w ≤
          N.connection.ricci (e (u • theta)) w w := by
    intro u hu w
    simpa only [Nat.cast_one] using hRic u hu w
  exact RiemannianMetric.polarDensity_cross_le_on_regular_ray
    (m := 1) N.metric N.connection one_pos hU h0 he hgeo hmetric theta htheta
    hb hkappa hsub hinj hRic' ht hs hts

theorem m64Intrinsic_polarDensity_cross_le_of_curvature_norm
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U, RiemannianMetric.IsGeodesicOn N.metric
      (fun s : ℝ => e (s • v))
      {s : ℝ | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0)
        (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b kappa : ℝ} (hb : 0 < b) (hkappa : 0 ≤ kappa)
    (hsub : ∀ s ∈ Icc (0 : ℝ) b, s • theta ∈ U)
    (hinj : ∀ s ∈ Icc (0 : ℝ) b,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (s • theta)))
    (hcurv : ∀ p ∈ standardAnnulusDomain,
      N.connection.curvatureTensorNorm p ≤ kappa)
    (hmap : ∀ s ∈ Ioo (0 : ℝ) b,
      e (s • theta) ∈ standardAnnulusDomain)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) b)
    (hs : s ∈ Ioo (0 : ℝ) b) (hts : t ≤ s) :
    (s ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (s • theta)) *
        modelS kappa t ^ (1 : ℕ) ≤
      (t ^ (1 : ℕ) * N.metric.pullbackVolumeDensity e (t • theta)) *
        modelS kappa s ^ (1 : ℕ) := by
  apply m64Intrinsic_polarDensity_cross_le_of_ricci N hU h0 he hgeo hmetric
    theta htheta hb hkappa hsub hinj
  · intro u hu w
    have hric := m64Intrinsic_radial_ricci_lower_of_curvature_norm
      N kappa hcurv hmap u hu w
    simpa only [Nat.cast_one, one_mul] using hric
  · exact ht
  · exact hs
  · exact hts

end PoincareConjecture
