import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ScalarJacobi
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RadialSystem
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Center

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_radialCurvature_transverse_pairing
    (N : IntrinsicAnnulus) (p : AnnulusCoordinates)
    (P : AnnulusCoordinates →L[ℝ] AnnulusCoordinates) (hi : P.IsInvertible)
    (hP : ∀ u v, N.metric.inner p (P u) (P v) = inner ℝ u v)
    (theta nu w : AnnulusCoordinates)
    (htheta : inner ℝ theta theta = 1) (horth : inner ℝ theta nu = 0) :
    inner ℝ nu (P.inverse (N.metric.radialCurvatureOperator p (P theta) (P w))) =
      N.connection.scalarCurvature p / 2 * inner ℝ nu w := by
  calc
    _ = N.metric.inner p (P nu)
        (P (P.inverse (N.metric.radialCurvatureOperator p (P theta) (P w)))) :=
      (hP nu _).symm
    _ = N.metric.inner p (N.connection.curvature p (P w) (P theta) (P theta))
        (P nu) := by
      rw [hi.self_apply_inverse, N.metric.radialCurvatureOperator_apply N.connection,
        N.metric.symm]
    _ = N.connection.curvatureTensor p (P w) (P theta) (P nu) (P theta) := rfl
    _ = N.connection.scalarCurvature p / 2 * inner ℝ nu w := by
      rw [N.connection.curvatureTensor_eq_half_scalarCurvature]
      simp only [hP, htheta, horth, mul_one, mul_zero, sub_zero]
      rw [real_inner_comm w nu]

theorem m64Intrinsic_hasDerivAt_transverse_jacobi
    (N : IntrinsicAnnulus) (p : AnnulusCoordinates)
    (P : AnnulusCoordinates →L[ℝ] AnnulusCoordinates) (hi : P.IsInvertible)
    (hP : ∀ u v, N.metric.inner p (P u) (P v) = inner ℝ u v)
    (theta nu : AnnulusCoordinates)
    (htheta : inner ℝ theta theta = 1) (horth : inner ℝ theta nu = 0)
    {A V : ℝ → AnnulusCoordinates →L[ℝ] AnnulusCoordinates} {t : ℝ}
    (hV : HasDerivAt V
      (-((P.inverse.comp ((N.metric.radialCurvatureOperator p (P theta)).comp P)).comp
        (A t))) t) :
    HasDerivAt (fun s => inner ℝ nu (V s nu))
      (-(N.connection.scalarCurvature p / 2) * inner ℝ nu (A t nu)) t := by
  have hv := hV.clm_apply (hasDerivAt_const t nu)
  have h := (hasDerivAt_const t nu).inner ℝ hv
  simp only [map_zero, add_zero, inner_zero_left] at h
  change HasDerivAt (fun s => inner ℝ nu (V s nu))
    (inner ℝ nu (-(P.inverse
      (N.metric.radialCurvatureOperator p (P theta) (P (A t nu)))))) t at h
  rw [inner_neg_right,
    m64Intrinsic_radialCurvature_transverse_pairing N p P hi hP theta nu _ htheta horth,
    ← neg_mul] at h
  exact h

theorem m64Intrinsic_exists_radial_scalar_jacobi
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b : ℝ} (hb : 0 < b) (hsub : ∀ s ∈ Icc 0 b, s • theta ∈ U) :
    ∃ j v : ℝ → ℝ,
      j 0 = 0 ∧
      (∀ t ∈ Icc 0 b, HasDerivAt j (v t) t) ∧
      (∀ t ∈ Icc 0 b, HasDerivAt v
        (-(N.connection.scalarCurvature (e (t • theta)) / 2) * j t) t) ∧
      (∀ t ∈ Icc 0 b, ContDiffAt ℝ ∞ j t) ∧
      ∀ t ∈ Ioc 0 b, |j t| = t * N.metric.pullbackVolumeDensity e (t • theta) := by
  obtain ⟨basis, hbasis⟩ :=
    RiemannianMetric.exists_orthonormalBasis_radial (m := 1) theta htheta
  subst theta
  obtain ⟨P, _hP0, hPi, hpair, hrad, hA0, hA, hV⟩ :=
    N.metric.exists_radial_parallel_jacobi N.connection hU h0 he hgeo hmetric
      (basis 0) hb hsub
  let A : ℝ → AnnulusCoordinates →L[ℝ] AnnulusCoordinates :=
    fun t => (P t).inverse.comp (t • mfderiv (𝓡 2) (𝓡 2) e (t • basis 0))
  let j : ℝ → ℝ := fun t => inner ℝ (basis 1) (A t (basis 1))
  let v : ℝ → ℝ := fun t => inner ℝ (basis 1) (deriv A t (basis 1))
  refine ⟨j, v, ?_, ?_, ?_, ?_, ?_⟩
  · change inner ℝ (basis 1) (A 0 (basis 1)) = 0
    change A 0 = 0 at hA0
    rw [hA0]
    simp only [zero_apply, inner_zero_right]
  · intro t ht
    have hd : HasDerivAt A (deriv A t) t :=
      ((hA t ht).differentiableAt (by simp)).hasDerivAt
    simpa only [j, v, map_zero, add_zero, inner_zero_left] using
      (hasDerivAt_const t (basis 1)).inner ℝ
        (hd.clm_apply (hasDerivAt_const t (basis 1)))
  · intro t ht
    exact m64Intrinsic_hasDerivAt_transverse_jacobi N (e (t • basis 0))
      (P t) (hPi t ht) (hpair t ht) (basis 0) (basis 1)
      (by simp)
      (by simp only [basis.inner_eq_ite, Fin.zero_ne_one, if_false]) (hV t ht)
  · intro t ht
    exact contDiffAt_const.inner ℝ ((hA t ht).clm_apply contDiffAt_const)
  · intro t ht
    have hd := N.metric.abs_det_transverse_radialDifferential_of_isInvertible
      e basis ht.1 (P t) (hPi t ⟨ht.1.le, ht.2⟩)
        (hpair t ⟨ht.1.le, ht.2⟩) (hrad t ⟨ht.1.le, ht.2⟩).symm
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      basis.coe_toBasis, basis.coe_toBasis_repr_apply, basis.repr_apply_apply,
      Fin.succ_zero_eq_one, pow_one, j, A] using! hd

theorem m64Intrinsic_polarDensity_jacobi
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b t : ℝ} (hb : 0 < b) (hsub : ∀ s ∈ Icc 0 b, s • theta ∈ U)
    (ht : t ∈ Ioo 0 b)
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (t • theta))) :
    let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
    deriv (deriv y) t + N.connection.scalarCurvature (e (t • theta)) / 2 * y t = 0 := by
  let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
  change deriv (deriv y) t + N.connection.scalarCurvature (e (t • theta)) / 2 * y t = 0
  obtain ⟨j, v, _hj0, hj, hv, hjc, hdensity⟩ :=
    m64Intrinsic_exists_radial_scalar_jacobi N hU h0 he hgeo hmetric theta htheta hb hsub
  have ht' : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
  have hjv : deriv j =ᶠ[𝓝 t] v := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hj s ⟨hs.1.le, hs.2.le⟩).deriv
  have hj2 : deriv (deriv j) t =
      -(N.connection.scalarCurvature (e (t • theta)) / 2) * j t :=
    ((hv t ht').congr_of_eventuallyEq hjv).deriv
  have hyr : 0 < y t := by
    exact mul_pos ht.1 (N.metric.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (hU.mem_nhds (hsub t ht'))) hi).2
  have hne : j t ≠ 0 := by
    apply abs_pos.mp
    rw [hdensity t ⟨ht.1, ht.2.le⟩]
    exact hyr
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have heq : -j =ᶠ[𝓝 t] y := by
      filter_upwards [isOpen_Ioo.mem_nhds ht,
        (hjc t ht').continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)] with s hs hjs
      change -j s = y s
      exact (abs_of_neg hjs).symm.trans (hdensity s ⟨hs.1, hs.2.le⟩)
    have hd := heq.deriv.deriv_eq
    have hnegd : deriv (deriv (-j)) t = -deriv (deriv j) t := by
      rw [deriv.neg']
      exact deriv.neg
    rw [hnegd, hj2] at hd
    have hyval : -j t = y t := heq.self_of_nhds
    rw [← hd, ← hyval]
    ring
  · have heq : j =ᶠ[𝓝 t] y := by
      filter_upwards [isOpen_Ioo.mem_nhds ht,
        (hjc t ht').continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)] with s hs hjs
      exact (abs_of_pos hjs).symm.trans (hdensity s ⟨hs.1, hs.2.le⟩)
    have hd := heq.deriv.deriv_eq
    have hyval := heq.self_of_nhds
    rw [← hd, hj2, ← hyval]
    ring

theorem m64Intrinsic_polarDensity_log_derivative_ge_sqrt_max_cot
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {b t : ℝ} (hb : 0 < b)
    (hbpi : Real.sqrt (max K 1) * b ≤ Real.pi)
    (hsub : ∀ s ∈ Icc 0 b, s • theta ∈ U)
    (hi : ∀ s ∈ Icc 0 b,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (s • theta)))
    (hmap : ∀ s ∈ Ioo 0 b, e (s • theta) ∈ standardAnnulusDomain)
    (ht : t ∈ Ioo 0 b) :
    let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
    Real.sqrt (max K 1) * Real.cos (Real.sqrt (max K 1) * t) /
        Real.sin (Real.sqrt (max K 1) * t) ≤ deriv y t / y t := by
  let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
  have hy (s : ℝ) (hs : s ∈ Icc 0 b) : ContDiffAt ℝ ∞ y s := by
    simpa only [Nat.cast_one, div_one, Real.rpow_one] using
      N.metric.contDiffAt_signed_polarDensityRoot theta 1
        (he.contMDiffAt (hU.mem_nhds (hsub s hs))) (hi s hs)
  have hy' (s : ℝ) (hs : s ∈ Icc 0 b) : ContDiffAt ℝ ∞ (deriv y) s :=
    (hy s hs).derivWithin (by simp)
  apply m64Intrinsic_jacobi_log_derivative_ge_sqrt_max_cot_of_gaussian N K hK hb hbpi
    (q := fun s => e (s • theta)) (J := y) (J' := deriv y) (J'' := deriv (deriv y))
    hmap
    (fun s hs => ((hy s hs).differentiableAt (by simp)).hasDerivAt)
    (fun s hs => (hy' s hs).continuousAt.continuousWithinAt)
    (fun s hs => ((hy' s ⟨hs.1.le, hs.2.le⟩).differentiableAt (by simp)).hasDerivAt)
    (by simp only [y, zero_mul])
    (fun s hs => mul_pos hs.1 (N.metric.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (hU.mem_nhds (hsub s ⟨hs.1.le, hs.2.le⟩)))
        (hi s ⟨hs.1.le, hs.2.le⟩)).2)
    (fun s hs => m64Intrinsic_polarDensity_jacobi N hU h0 he hgeo hmetric theta
      htheta hb hsub hs (hi s ⟨hs.1.le, hs.2.le⟩)) ht

end PoincareConjecture
