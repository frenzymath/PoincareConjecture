import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

theorem m64Intrinsic_scaled_jacobi_log_derivative_ge_cot_Ioc
    {R kappa : ℝ} (hR : 0 < R) (hkappa : 0 < kappa)
    (hRpi : kappa * R < Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioc (0 : ℝ) R, 0 < J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ kappa ^ 2)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) R) :
    kappa * Real.cos (kappa * t) / Real.sin (kappa * t) ≤ J' t / J t := by
  have hW := m64Intrinsic_scaled_spherical_wronskian_nonneg_of_jacobi
    hR hkappa.le hRpi.le hJ hJ' hJ'' hzero
    (fun s hs => (hpos s ⟨hs.1, hs.2.le⟩).le) hjac hk t ⟨ht.1.le, ht.2⟩
  have hsin : 0 < Real.sin (kappa * t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hkappa ht.1)
      ((mul_le_mul_of_nonneg_left ht.2 hkappa.le).trans_lt hRpi)
  apply (div_le_div_iff₀ hsin (hpos t ht)).mpr
  nlinarith

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_polarDensity_log_derivative_ge_sqrt_max_cot_Ioc
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
    (hbpi : Real.sqrt (max K 1) * b < Real.pi)
    (hsub : ∀ s ∈ Icc 0 b, s • theta ∈ U)
    (hmap : ∀ s ∈ Ioo 0 b, e (s • theta) ∈ standardAnnulusDomain)
    (ht : t ∈ Ioc 0 b) :
    let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
    Real.sqrt (max K 1) * Real.cos (Real.sqrt (max K 1) * t) /
      Real.sin (Real.sqrt (max K 1) * t) ≤ deriv y t / y t := by
  have hmax : 0 ≤ max K 1 := le_trans zero_le_one (le_max_right K 1)
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right K 1))
  have hKkappa : K ≤ Real.sqrt (max K 1) ^ 2 := by
    rw [Real.sq_sqrt hmax]
    exact le_max_left K 1
  have hi := m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper N K
    (Real.sqrt (max K 1)) hK hkappa hKkappa hU h0 he hgeo hmetric
    theta htheta hb hbpi hsub hmap
  let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • theta)
  have hy (s : ℝ) (hs : s ∈ Icc 0 b) : ContDiffAt ℝ ∞ y s := by
    simpa only [Nat.cast_one, div_one, Real.rpow_one] using
      N.metric.contDiffAt_signed_polarDensityRoot theta 1
        (he.contMDiffAt (hU.mem_nhds (hsub s hs))) (hi s hs)
  have hy' (s : ℝ) (hs : s ∈ Icc 0 b) : ContDiffAt ℝ ∞ (deriv y) s :=
    (hy s hs).derivWithin (by simp)
  apply m64Intrinsic_scaled_jacobi_log_derivative_ge_cot_Ioc hb hkappa hbpi
    (J := y) (J' := deriv y) (J'' := deriv (deriv y))
    (k := fun s => N.connection.scalarCurvature (e (s • theta)) / 2)
    (fun s hs => ((hy s hs).differentiableAt (by simp)).hasDerivAt)
    (fun s hs => (hy' s hs).continuousAt.continuousWithinAt)
    (fun s hs => ((hy' s ⟨hs.1.le, hs.2.le⟩).differentiableAt (by simp)).hasDerivAt)
    (by simp only [y, zero_mul])
    (fun s hs => mul_pos hs.1 (N.metric.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (hU.mem_nhds (hsub s ⟨hs.1.le, hs.2⟩)))
        (hi s ⟨hs.1.le, hs.2⟩)).2)
    (fun s hs => m64Intrinsic_polarDensity_jacobi N hU h0 he hgeo hmetric theta
      htheta hb hsub hs (hi s ⟨hs.1.le, hs.2.le⟩))
    (fun s hs => (hK (e (s • theta)) (hmap s hs)).trans hKkappa) ht

theorem m64Intrinsic_focusing_pairing_ge_of_gaussian_upper_Ioc
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (hgauss : ∀ v ∈ U, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    (basis : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {b r : ℝ} (hb : 0 < b) (hbpi : Real.sqrt (max K 1) * b < Real.pi)
    (hsub : ∀ s ∈ Icc 0 b, s • basis 0 ∈ U)
    (hmap : ∀ s ∈ Ioo 0 b, e (s • basis 0) ∈ standardAnnulusDomain)
    (hr : r ∈ Ioc 0 b) (w : AnnulusCoordinates) :
    let kappa := Real.sqrt (max K 1)
    let B := N.metric.pullbackCoefficients e
    let Y : AnnulusCoordinates → AnnulusCoordinates :=
      fun x => (Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)) • x
    Real.cos (kappa * r) * B (r • basis 0) w w ≤
      B (r • basis 0) (fderiv ℝ Y (r • basis 0) w +
        coordinateChristoffel B (r • basis 0) w (Y (r • basis 0))) w := by
  have hmax : 0 ≤ max K 1 := le_trans zero_le_one (le_max_right K 1)
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right K 1))
  have hKkappa : K ≤ Real.sqrt (max K 1) ^ 2 := by
    rw [Real.sq_sqrt hmax]
    exact le_max_left K 1
  have hi := m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper N K
    (Real.sqrt (max K 1)) hK hkappa hKkappa hU h0 he hgeo hmetric
    (basis 0) (basis.norm_eq_one 0) hb hbpi hsub hmap
  have hr' : r ∈ Icc 0 b := ⟨hr.1.le, hr.2⟩
  have hgs : ∀ᶠ s in 𝓝 r, ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (s • basis 0) (s • basis 0) v =
        inner ℝ (s • basis 0) v := by
    have hc : ContinuousAt (fun s : ℝ => s • basis 0) r := by fun_prop
    filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds (hsub r hr'))] with s hs v
    exact hgauss _ hs v
  apply m64Intrinsic_focusing_pairing_ge_of_log_derivative N basis hr.1 hkappa
    ((mul_le_mul_of_nonneg_left hr.2 hkappa.le).trans_lt hbpi)
    (he.contMDiffAt (hU.mem_nhds (hsub r hr'))) (hi r hr') hgs
  exact m64Intrinsic_polarDensity_log_derivative_ge_sqrt_max_cot_Ioc N K hK
    hU h0 he hgeo hmetric (basis 0) (basis.norm_eq_one 0) hb hbpi hsub hmap hr

end PoincareConjecture
