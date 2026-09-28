import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EarliestConfinedContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConfinedDigonPerturbation





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture





theorem m64Intrinsic_confined_radial_eq_canonical
    (N : IntrinsicAnnulus) {K kappa R B : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi / 2)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2) (hshort : kappa * R < Real.pi)
    (hB : 0 < B) (hBR : B ≤ R)
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
    (hcorner : ∀ᶠ z in 𝓝 (e 0), z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2)
    {theta : AnnulusCoordinates} (htheta : ‖theta‖ = 1)
    (hthetaConf : ∀ s ∈ Icc 0 B, e (s • theta) ∈ closure U) :
    ∀ s ∈ Icc 0 B, ∀ v : AnnulusCoordinates,
      ‖v‖ ≤ R → (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) →
        e v = e (s • theta) → v = s • theta := by
  intro t ht w hwR hwconf hwpoint
  by_contra hne
  have hsmall' : max K 0 * intrinsicAnnulusArea N.metric < Real.pi :=
    hsmall.trans (by linarith [Real.pi_pos])
  obtain ⟨s, hs, v, hv, hvne, hvR, hvconf, hvpoint, _, hvi, hmeet, hmin⟩ :=
    m64Intrinsic_exists_earliest_confined_contact N hK hsmall' hkappa hKkappa hshort hB hBR
      hU hV hpV hbV hUV hcover hfront hsub hOmega hzeroOmega he heBall hmetric hgeo hstar
      hcontains L hphi hzero hcorner htheta hthetaConf ⟨t, ht, w, ⟨hwR, hwconf⟩, hwpoint, hne⟩
  have hcanonicalConf : ∀ a ∈ Icc (0 : ℝ) 1, e (a • s • theta) ∈ closure U := by
    intro a ha
    rw [smul_smul]
    exact hthetaConf (a * s) ⟨mul_nonneg ha.1 hs.1.le,
      (mul_le_mul_of_nonneg_right ha.2 hs.1.le).trans (by simpa only [one_mul] using hs.2)⟩
  have hcanonicalNorm : ‖s • theta‖ ≤ R := by
    simpa only [norm_smul, Real.norm_of_nonneg hs.1.le, htheta, mul_one] using hs.2.trans hBR
  have hsv := hcontains (s • theta) hcanonicalNorm hcanonicalConf
  obtain ⟨b, hb, z, hzR, hzconf, hzpoint, hzne⟩ :=
    m64Intrinsic_confined_digon_has_earlier_contact N hK hsmall hkappa hKkappa hshort
      hU hV hpV hbV hUV hcover hfront hsub hOmega hzeroOmega he hmetric hgeo hstar
      hv hvne hvR hvconf hvi htheta hs.1 hsv
      (fun a ha => hthetaConf a ⟨ha.1, ha.2.trans hs.2⟩) hvpoint hmeet (hgauss v hv)
      L hphi hzero hcorner
  exact hb.2.not_ge (hmin b ⟨hb.1.le, hb.2.le.trans hs.2⟩ z ⟨hzR, hzconf⟩ hzpoint hzne)

end PoincareConjecture
