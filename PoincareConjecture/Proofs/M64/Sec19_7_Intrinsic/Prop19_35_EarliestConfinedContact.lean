import PoincareConjecture.Proofs.M64.Mathlib.LeastConfinedRadialContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConfinedRadialInverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ClosedCornerRadialInjectivity






noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture





theorem m64Intrinsic_exists_earliest_confined_contact
    (N : IntrinsicAnnulus) {K kappa R B : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2) (hshort : kappa * R < Real.pi)
    (hB : 0 < B) (hBR : B ≤ R)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzeroOmega : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (heBall : ContinuousOn e (closedBall 0 R))
    (hmetric : ∀ u w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ u w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    (hcontains : ∀ v : AnnulusCoordinates, ‖v‖ ≤ R →
      (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) → v ∈ Omega)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (e 0)) (hzero : phi (e 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (e 0), z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2)
    {theta : AnnulusCoordinates} (htheta : ‖theta‖ = 1)
    (hthetaConf : ∀ s ∈ Icc 0 B, e (s • theta) ∈ closure U)
    (hex : ∃ s ∈ Icc 0 B, ∃ v : AnnulusCoordinates,
      (‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) ∧
        e v = e (s • theta) ∧ v ≠ s • theta) :
    ∃ s ∈ Ioc 0 B, ∃ v : AnnulusCoordinates,
      v ∈ Omega ∧ v ≠ 0 ∧ ‖v‖ ≤ R ∧
      (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) ∧
      e v = e (s • theta) ∧ v ≠ s • theta ∧
      InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc 0 s,
        e (t • v) = e (u • theta) → (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = s)) ∧
      ∀ u ∈ Icc 0 B, ∀ w : AnnulusCoordinates,
        (‖w‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • w) ∈ closure U) →
          e w = e (u • theta) → w ≠ u • theta → s ≤ u := by
  have hcanonicalNorm (s : ℝ) (hs : s ∈ Icc 0 B) : ‖s • theta‖ ≤ R := by
    simpa only [norm_smul, Real.norm_of_nonneg hs.1, htheta, mul_one] using hs.2.trans hBR
  have hcanonicalConf (s : ℝ) (hs : s ∈ Icc 0 B) :
      ∀ t ∈ Icc (0 : ℝ) 1, e (t • s • theta) ∈ closure U := by
    intro t ht
    rw [smul_smul]
    exact hthetaConf (t * s) ⟨mul_nonneg ht.1 hs.1,
      (mul_le_mul_of_nonneg_right ht.2 hs.1).trans (by simpa only [one_mul] using hs.2)⟩
  have hlocal : ∀ s ∈ Icc 0 B, ∃ W ∈ 𝓝 (s • theta), InjOn e W := by
    intro s hs
    have hv := hcontains (s • theta) (hcanonicalNorm s hs) (hcanonicalConf s hs)
    obtain ⟨F, hvF, _, hF, _, _⟩ := m64Intrinsic_exists_short_confined_radial_inverse N
      hK hkappa hKkappa hOmega hzeroOmega he hmetric hgeo hstar hv
      ((mul_le_mul_of_nonneg_left (hcanonicalNorm s hs) hkappa.le).trans_lt hshort)
      (fun t ht => hsub (hcanonicalConf s hs t ht))
    exact ⟨F.source, F.open_source.mem_nhds hvF, by simpa only [hF] using F.injOn⟩
  have hradialInj (v : AnnulusCoordinates) (hvR : ‖v‖ ≤ R)
      (hvconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U) (hvne : v ≠ 0) :
      InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1) :=
    m64Intrinsic_closed_corner_radial_injOn N hK hsmall hU hV hpV hbV hUV hcover hfront
      hsub hOmega hzeroOmega he hmetric hgeo hstar (hcontains v hvR hvconf) hvne
      hvconf L hphi hzero hcorner
  have hBne : B • theta ≠ 0 := by
    intro hz
    have hn := congrArg norm hz
    simp only [norm_smul, Real.norm_of_nonneg hB.le, htheta, mul_one, norm_zero] at hn
    exact hB.ne' hn
  have hcanInj := m64_radial_injOn_of_positive_rescale e hB
    (hradialInj (B • theta) (hcanonicalNorm B ⟨hB.le, le_rfl⟩)
      (hcanonicalConf B ⟨hB.le, le_rfl⟩) hBne)
  obtain ⟨s, hs, v, hv, heq, hne, hmin⟩ :=
    m64_exists_least_noncanonical_confined_ray heBall isClosed_closure htheta hBR hlocal hex
  have hvne : v ≠ 0 := by
    intro hz
    have h0s := hcanInj ⟨le_rfl, hB.le⟩ hs
      (by simpa only [hz, zero_smul] using heq)
    exact hne (by simp only [hz, h0s.symm, zero_smul])
  have hi := hradialInj v hv.1 hv.2 hvne
  obtain ⟨hspos, _, hcontacts⟩ := m64_least_confined_contact_has_only_endpoint_contacts
    e hs hv.1 hv.2 heq hne hi hcanInj hmin
  exact ⟨s, ⟨hspos, hs.2⟩, v, hcontains v hv.1 hv.2, hvne, hv.1, hv.2,
    heq, hne, hi, hcontacts, hmin⟩

end PoincareConjecture
