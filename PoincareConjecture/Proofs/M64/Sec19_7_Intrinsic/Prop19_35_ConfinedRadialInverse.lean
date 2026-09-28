import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_confined_radial_differential_injective
    (N : IntrinsicAnnulus) {K kappa : ℝ} (hK : N.GaussianCurvatureBound K)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzero : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (hmetric : ∀ u w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ u w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    {v : AnnulusCoordinates} (hv : v ∈ Omega) (hshort : kappa * ‖v‖ < Real.pi)
    (hconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (t • v)) := by
  by_cases hz : v = 0
  · subst v
    intro t _
    have hi0 := m64Intrinsic_mfderiv_injective_of_pullbackDensity_pos N
      (he.contMDiffAt (hOmega.mem_nhds hzero)) (by
        rw [N.metric.pullbackVolumeDensity_zero_eq_one e hmetric]
        exact zero_lt_one)
    simpa only [TangentSpace, mfderiv_eq_fderiv, smul_zero] using hi0
  have hell : 0 < ‖v‖ := norm_pos_iff.mpr hz
  let theta : AnnulusCoordinates := ‖v‖⁻¹ • v
  have htheta : ‖theta‖ = 1 := by
    dsimp only [theta]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hell.le),
      inv_mul_cancel₀ hell.ne']
  have hscale (s : ℝ) : s • theta = (s / ‖v‖) • v := by
    simp only [theta, smul_smul, div_eq_mul_inv]
  have htime (s : ℝ) (hs : s ∈ Icc 0 ‖v‖) : s / ‖v‖ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hell.le, (div_le_one hell).mpr hs.2⟩
  have hsub : ∀ s ∈ Icc 0 ‖v‖, s • theta ∈ Omega := by
    intro s hs
    rw [hscale]
    exact hstar v hv _ (htime s hs)
  have hmap : ∀ s ∈ Ioo 0 ‖v‖, e (s • theta) ∈ standardAnnulusDomain := by
    intro s hs
    rw [hscale]
    exact hconf _ (htime s (Ioo_subset_Icc_self hs))
  have hi := m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper N K kappa
    hK hkappa hKkappa hOmega hzero he hgeo hmetric theta htheta hell hshort hsub hmap
  intro t ht
  have htl : t * ‖v‖ ∈ Icc 0 ‖v‖ := by
    refine ⟨mul_nonneg ht.1 hell.le, ?_⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hell.le
  have hi' : Function.Injective (fderiv ℝ e ((t * ‖v‖) • theta)) := by
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi (t * ‖v‖) htl
  rw [hscale, mul_div_cancel_right₀ _ hell.ne'] at hi'
  simpa only [TangentSpace, mfderiv_eq_fderiv] using hi'




theorem m64Intrinsic_exists_short_confined_radial_inverse
    (N : IntrinsicAnnulus) {K kappa : ℝ} (hK : N.GaussianCurvatureBound K)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzero : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (hmetric : ∀ u w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ u w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    {v : AnnulusCoordinates} (hv : v ∈ Omega) (hshort : kappa * ‖v‖ < Real.pi)
    (hconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      v ∈ F.source ∧ F.source ⊆ Omega ∧ (F : AnnulusCoordinates → AnnulusCoordinates) = e ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target := by
  have hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e v) := by
    simpa only [TangentSpace, mfderiv_eq_fderiv, one_smul] using
      m64Intrinsic_confined_radial_differential_injective N hK hkappa hKkappa
        hOmega hzero he hmetric hgeo hstar hv hshort hconf 1 ⟨zero_le_one, le_rfl⟩
  exact m64Intrinsic_exists_smooth_polar_inverse hOmega he hv hi

end PoincareConjecture
