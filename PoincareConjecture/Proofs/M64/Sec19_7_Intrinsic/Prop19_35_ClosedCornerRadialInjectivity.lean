import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ClosedRadialGeodesic
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ClosedCornerRayInjectivity












noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_closed_corner_radial_injOn
    (N : IntrinsicAnnulus) {K : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hd : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzeroOmega : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (hmetric : ∀ v w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    {v : AnnulusCoordinates} (hv : v ∈ Omega) (hne : v ≠ 0)
    (hconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ closure U)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (e 0))
    (hzero : phi (e 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (e 0),
      z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1) := by
  have hell : 0 < ‖v‖ := norm_pos_iff.mpr hne
  obtain ⟨g, hg, hggeo, hunit, hg0, _, hgvalue, hvalue, _⟩ :=
    m64Intrinsic_exists_closed_radial_unit_geodesic N hOmega hzeroOmega he
      hmetric hgeo hstar hv hne
  have hgconf : MapsTo g (Icc 0 ‖v‖) (closure U) := by
    intro t ht
    rw [hgvalue t ht]
    exact hconf _ ⟨div_nonneg ht.1 hell.le, (div_le_one hell).mpr ht.2⟩
  have hginj := m64Intrinsic_closed_corner_ray_injOn N hK hsmall
    hU hV hpV hbV hd hcover hfront hsub hg hggeo hunit hgconf L
    (by simpa only [hg0] using hphi) (by simpa only [hg0] using hzero)
    (by simpa only [hg0] using hcorner)
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖v‖ * t ∈ Icc 0 ‖v‖ := by
    refine ⟨mul_nonneg hell.le ht.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hell.le
  intro s hs t ht hst
  have heq := hginj (htime s hs) (htime t ht)
    ((hvalue s hs).trans (hst.trans (hvalue t ht).symm))
  exact mul_left_cancel₀ hell.ne' heq

end PoincareConjecture
