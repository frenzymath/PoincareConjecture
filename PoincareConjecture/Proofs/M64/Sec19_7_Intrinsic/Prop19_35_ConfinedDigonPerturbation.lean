import PoincareConjecture.Proofs.M64.Mathlib.RadialArcDerivative
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialDigonPerturbation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConfinedDigonConvexity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialDigonGeodesics
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactRadialInverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConfinedRadialInverse





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_confined_digon_has_earlier_contact
    (N : IntrinsicAnnulus) {K kappa R s : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi / 2)
    (hkappa : 0 < kappa) (hKkappa : K ≤ kappa ^ 2) (hshort : kappa * R < Real.pi)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzeroOmega : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (hmetric : ∀ u w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ u w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    {v theta : AnnulusCoordinates} (hv : v ∈ Omega) (hvne : v ≠ 0) (hvR : ‖v‖ ≤ R)
    (hvconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U)
    (hvi : InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1))
    (htheta : ‖theta‖ = 1) (hs : 0 < s) (hsv : s • theta ∈ Omega)
    (hthetaconf : ∀ t ∈ Icc 0 s, e (t • theta) ∈ closure U)
    (hend : e v = e (s • theta))
    (hmeet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc 0 s,
      e (t • v) = e (b • theta) → (t = 0 ∧ b = 0) ∨ (t = 1 ∧ b = s))
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (e 0)) (hzero : phi (e 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (e 0), z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    ∃ b ∈ Ioo 0 s, ∃ z : AnnulusCoordinates,
      ‖z‖ ≤ R ∧ (∀ t ∈ Icc (0 : ℝ) 1, e (t • z) ∈ closure U) ∧
        e z = e (b • theta) ∧ z ≠ b • theta := by
  have hell : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hsmall' : max K 0 * intrinsicAnnulusArea N.metric < Real.pi :=
    hsmall.trans (by linarith [Real.pi_pos])
  obtain ⟨alpha, beta, ha, hb, hga, hgb, hua, hub, ha0, hb0, haT, hbs,
      hav, hbv, hcontacts, had, _⟩ := m64Intrinsic_exists_radial_digon_geodesics
    N hOmega hzeroOmega he hmetric hgeo hstar hv hvne htheta hs hsv hend hmeet
  have haconf : MapsTo alpha (Icc 0 ‖v‖) (closure U) := by
    intro t ht
    rw [hav t ht]
    exact hvconf _ ⟨div_nonneg ht.1 hell.le, (div_le_one hell).mpr ht.2⟩
  have hbconf : MapsTo beta (Icc 0 s) (closure U) := by
    intro t ht
    rw [hbv t ht]
    exact hthetaconf t ht
  obtain ⟨W, Y, _, _, _, _, _, _, _, _, hfW, _, _, _, hclWU, hfan,
      ⟨phi0, L0, hd0, hz0, haxis0a, haxis0b, hcorner0⟩,
      phi1, L1, hd1, hz1, haxis1a, _, hcorner1⟩ :=
    m64Intrinsic_confined_digon_convex_coordinates N hK hsmall' hU hV hpV hbV hUV
      hcover hfront hsub ha hb hell hs hga hgb (hb0.trans ha0.symm) (hbs.trans haT.symm)
      hcontacts hua hub haconf hbconf L (ha0.symm ▸ hphi) (ha0.symm ▸ hzero)
      (ha0.symm ▸ hcorner)
  have hbi := m64Intrinsic_closed_corner_ray_injOn N hK hsmall' hU hV hpV hbV hUV
    hcover hfront hsub hb hgb hub hbconf L (hb0.symm ▸ hphi) (hb0.symm ▸ hzero)
      (hb0.symm ▸ hcorner)
  have hreg := m64Intrinsic_confined_radial_differential_injective N hK hkappa hKkappa
    hOmega hzeroOmega he hmetric hgeo hstar hv
      ((mul_le_mul_of_nonneg_left hvR hkappa.le).trans_lt hshort)
      (fun t ht => hsub (hvconf t ht))
  obtain ⟨F, hFs, _, hFe, _, hFi⟩ :=
    m64Intrinsic_exists_compact_radial_inverse hOmega he (hstar v hv) hvi hreg
  have he0 : DifferentiableAt ℝ e 0 :=
    ((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
      (hOmega.mem_nhds hzeroOmega)).differentiableAt (by simp)
  have hev : DifferentiableAt ℝ e v :=
    ((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
      (hOmega.mem_nhds hv)).differentiableAt (by simp)
  have hada0 : deriv alpha 0 = fderiv ℝ e 0 (‖v‖⁻¹ • v) :=
    m64_deriv_eq_radial_of_eqOn_Icc he0 (ha.differentiable (by simp) 0) hell (by
      intro t ht
      simpa only [smul_smul, div_eq_mul_inv] using hav t ht)
  have hdb0 : deriv beta 0 = fderiv ℝ e 0 theta :=
    m64_deriv_eq_radial_of_eqOn_Icc he0 (hb.differentiable (by simp) 0) hs hbv
  have hde0 : fderiv ℝ e 0 v = ‖v‖ • deriv alpha 0 := by
    rw [hada0, map_smul, smul_smul, mul_inv_cancel₀ hell.ne', one_smul]
  have hdeT : fderiv ℝ e v v = ‖v‖ • deriv alpha ‖v‖ := by
    rw [had, map_smul, smul_smul, mul_inv_cancel₀ hell.ne', one_smul]
  have hinitv : L0 (fderiv ℝ e 0 v) = (‖v‖, 0) := by
    rw [hde0, map_smul, ← haxis0a, L0.apply_symm_apply]
    simp
  have hinittheta : L0 (fderiv ℝ e 0 theta) = (0, 1) := by
    rw [← hdb0, ← haxis0b, L0.apply_symm_apply]
  have htermcoord : L1 (deriv alpha ‖v‖) = (-1, 0) := by
    apply L1.symm.injective
    rw [L1.symm_apply_apply]
    rw [show ((-1, 0) : ℝ × ℝ) = -(1, 0) by simp]
    rw [map_neg, haxis1a, neg_neg]
  have hterminal : (L1 (fderiv ℝ e v v)).1 < 0 := by
    rw [hdeT, map_smul, htermcoord]
    simpa using neg_neg_of_pos hell
  have hacute : N.metric.cornerAngle (alpha ‖v‖)
      (-deriv alpha ‖v‖) (-deriv beta s) < Real.pi / 2 := by
    have hnonneg : 0 ≤ N.metric.cornerAngle (alpha 0) (deriv alpha 0) (deriv beta 0) :=
      Real.arccos_nonneg _
    linarith
  rw [N.metric.cornerAngle_neg_neg] at hacute
  have hpointangle := congrArg (fun p : AnnulusCoordinates =>
    N.metric.cornerAngle p (deriv alpha ‖v‖ : AnnulusCoordinates)
      (deriv beta s : AnnulusCoordinates)) haT
  rw [hpointangle] at hacute
  have hangle : N.metric.cornerAngle (e v) (fderiv ℝ e v v) (deriv beta s) < Real.pi / 2 := by
    rw [hdeT, N.metric.cornerAngle_smul_pos_left _ _ _ hell]
    exact hacute
  have hside : alpha '' Icc 0 ‖v‖ = (fun t : ℝ => e (t • v)) '' Icc 0 1 := by
    ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t / ‖v‖, ⟨div_nonneg ht.1 hell.le, (div_le_one hell).mpr ht.2⟩,
        (hav t ht).symm⟩
    · rintro ⟨t, ht, rfl⟩
      have htT : ‖v‖ * t ∈ Icc 0 ‖v‖ :=
        ⟨mul_nonneg hell.le ht.1, by nlinarith only [ht.2, hell]⟩
      refine ⟨‖v‖ * t, htT, ?_⟩
      rw [hav _ htT, mul_div_cancel_left₀ _ hell.ne']
  rw [hside] at hfW
  obtain ⟨b, hbI, z, hzR, hzconf, hzpoint, hzne⟩ :=
    m64Intrinsic_exists_earlier_radial_digon_contact N F hFe hFi hs hell hvR
      (fun t ht => hFs ⟨t, ht, rfl⟩) he0 hev hb hbi hb0 hbs hfW L0 L1
      (ha0 ▸ hd0) (ha0 ▸ hz0) (ha0 ▸ hcorner0) hinitv hinittheta
      (haT ▸ hd1) (haT ▸ hz1)
      (by simpa only [haT] using hcorner1.mono (fun _ hz hmem => (hz.mp hmem).1))
      hterminal hgauss hangle
  refine ⟨b, hbI, z, hzR, fun t ht => hclWU (hzconf t ht), ?_, hzne⟩
  exact hzpoint.trans (hbv b (Ioo_subset_Icc_self hbI))

end PoincareConjecture
