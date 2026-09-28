import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConfinedRadialUniqueness





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture






theorem m64Intrinsic_confined_radial_injOn
    (N : IntrinsicAnnulus) {K kappa R : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi / 2)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2) (hshort : kappa * R < Real.pi)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzeroOmega : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega) (heBall : ContinuousOn e (closedBall 0 R))
    (hmetric : ∀ u w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ u w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    (hcontains : ∀ v : AnnulusCoordinates, ‖v‖ ≤ R →
      (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) → v ∈ Omega)
    (hgauss : ∀ v ∈ Omega, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (e 0)) (hzero : phi (e 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (e 0), z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    InjOn e {v : AnnulusCoordinates |
      ‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U} := by
  intro v hv w hw heq
  by_cases hwzero : w = 0
  · subst w
    by_contra hvne
    have hsmall' : max K 0 * intrinsicAnnulusArea N.metric < Real.pi :=
      hsmall.trans (by linarith [Real.pi_pos])
    have hi := m64Intrinsic_closed_corner_radial_injOn N hK hsmall'
      hU hV hpV hbV hUV hcover hfront hsub hOmega hzeroOmega he hmetric hgeo hstar
      (hcontains v hv.1 hv.2) hvne hv.2 L hphi hzero hcorner
    have h10 := hi ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
      (by simpa only [one_smul, zero_smul] using heq)
    exact one_ne_zero h10
  have hB : 0 < ‖w‖ := norm_pos_iff.mpr hwzero
  let theta : AnnulusCoordinates := ‖w‖⁻¹ • w
  have htheta : ‖theta‖ = 1 := by
    simp only [theta, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hB.le),
      inv_mul_cancel₀ hB.ne']
  have htip : ‖w‖ • theta = w := by
    simp only [theta, smul_smul, mul_inv_cancel₀ hB.ne', one_smul]
  have hconf : ∀ s ∈ Icc 0 ‖w‖, e (s • theta) ∈ closure U := by
    intro s hs
    have hparam : s / ‖w‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hB.le, (div_le_one hB).mpr hs.2⟩
    simpa only [theta, smul_smul, div_eq_mul_inv] using hw.2 (s / ‖w‖) hparam
  have hcanonical := m64Intrinsic_confined_radial_eq_canonical N hK hsmall hkappa hKkappa
    hshort hB hw.1 hU hV hpV hbV hUV hcover hfront hsub hOmega hzeroOmega he heBall
    hmetric hgeo hstar hcontains hgauss L hphi hzero hcorner htheta hconf
    ‖w‖ ⟨hB.le, le_rfl⟩ v hv.1 hv.2 (by simpa only [htip] using heq)
  exact hcanonical.trans htip

end PoincareConjecture
