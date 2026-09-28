import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_SmoothNormalMap
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MetricGerm














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

private theorem normal_endpoint_geodesic_on
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hend : ∀ z : ℝ × ℝ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ gamma : ℝ → AnnulusCoordinates,
        G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
        gamma 0 = intrinsicAnnulusBoundary 1 z.1 ∧
        HasDerivAt gamma (z.2 • normal z.1) 0 ∧ gamma 1 = u z)
    {a lo hi : ℝ} (hzero : (0 : ℝ) ∈ Ioo lo hi)
    {gamma : ℝ → AnnulusCoordinates} (hgamma : G.IsGeodesicOn gamma (Ioo lo hi))
    (hinit : gamma 0 = intrinsicAnnulusBoundary 1 a)
    (hderiv : HasDerivAt gamma (normal a) 0) :
    G.IsGeodesicOn (fun t => u (a, t)) (Ioo lo hi) := by
  intro t ht
  obtain ⟨p, q, w, hlocal⟩ := hgamma t ht
  refine ⟨p, q, w, ?_⟩
  filter_upwards [hlocal, isOpen_Ioo.mem_nhds ht] with r hr hrI
  exact ⟨(m64Intrinsic_normal_endpoint_eq_geodesic G hend hzero hgamma hinit hderiv hrI).trans
    hr.1, hr.2⟩




theorem m64Intrinsic_exists_common_normal_geodesic_domain
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hnormal : ContDiff ℝ ∞ normal)
    (hend : ∀ z : ℝ × ℝ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ gamma : ℝ → AnnulusCoordinates,
        G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
        gamma 0 = intrinsicAnnulusBoundary 1 z.1 ∧
        HasDerivAt gamma (z.2 • normal z.1) 0 ∧ gamma 1 = u z)
    (a : ℝ) :
    ∃ S : Set ℝ, ∃ delta : ℝ, IsOpen S ∧ a ∈ S ∧ 0 < delta ∧
      ∀ s ∈ S, G.IsGeodesicOn (fun t => u (s, t)) (Ioo (-delta) 1) := by
  let A : IntrinsicAnnulus := ⟨G, G.euclideanLeviCivitaData⟩
  obtain ⟨S, delta, phase, hS, ha, hdelta, _, hinit, hflow, hgeo, _⟩ :=
    m64Intrinsic_exists_local_geodesic_variation A (m64Intrinsic_contDiff_boundary 1) hnormal a
  refine ⟨S, delta, hS, ha, hdelta, ?_⟩
  intro s hs
  have hz : (0 : ℝ) ∈ Ioo (-delta) delta := ⟨by linarith, hdelta⟩
  have hphase0 : (phase (s, 0)).1 = intrinsicAnnulusBoundary 1 s :=
    congrArg Prod.fst (hinit s hs)
  have hphased : HasDerivAt (fun t => (phase (s, t)).1) (normal s) 0 := by
    have h : HasDerivAt (fun t => (phase (s, t)).1) (phase (s, 0)).2 0 := by
      simpa [coordinateGeodesicField] using (hflow s hs 0 hz).hasFDerivAt.fst.hasDerivAt
    rw [show (phase (s, 0)).2 = normal s from congrArg Prod.snd (hinit s hs)] at h
    exact h
  have hnegative := normal_endpoint_geodesic_on G hend hz (hgeo s hs) hphase0 hphased
  obtain ⟨epsilon, hepsilon, gamma, hgamma, hgamma0, hgammaD, _⟩ := hend (s, 1)
  have hpositive := normal_endpoint_geodesic_on G hend
    (show (0 : ℝ) ∈ Ioo (-epsilon) (1 + epsilon) from ⟨by linarith, by linarith⟩)
    hgamma hgamma0 (by simpa only [one_smul] using hgammaD)
  intro t ht
  by_cases hlt : t < 0
  · exact hnegative t ⟨ht.1, hlt.trans hdelta⟩
  · exact hpositive t ⟨by linarith [le_of_not_gt hlt], by linarith [ht.2]⟩




theorem m64Intrinsic_exists_actual_normal_geodesic_neighborhood
    (N : IntrinsicAnnulus) (G : RiemannianMetric 2 AnnulusCoordinates)
    (hG : ∀ p ∈ standardAnnulusDomain,
      G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hnormal : ContDiff ℝ ∞ normal) (hu : ContDiff ℝ ∞ u)
    (hend : ∀ z : ℝ × ℝ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ gamma : ℝ → AnnulusCoordinates,
        G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
        gamma 0 = intrinsicAnnulusBoundary 1 z.1 ∧
        HasDerivAt gamma (z.2 • normal z.1) 0 ∧ gamma 1 = u z)
    {a b : ℝ} (hb : b < 1)
    (himage : ∀ t ∈ Icc (0 : ℝ) b, u (a, t) ∈ standardAnnulusDomain) :
    ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧ Icc (0 : ℝ) b ⊆ I ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I) ∧
      ∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I := by
  obtain ⟨S0, delta, hS0, ha0, hdelta, hgeo⟩ :=
    m64Intrinsic_exists_common_normal_geodesic_domain G hnormal hend a
  have hJsub : Icc (0 : ℝ) b ⊆ Ioo (-delta) 1 :=
    fun t ht => ⟨by linarith [ht.1], ht.2.trans_lt hb⟩
  obtain ⟨S, I, hS, hI, ha, hsub, hIJ, hmetric⟩ :=
    m64Intrinsic_exists_metric_agreement_tube N G hG hu.continuous isOpen_Ioo hJsub himage
  refine ⟨S ∩ S0, I, hS.inter hS0, hI, ⟨ha, ha0⟩, hsub,
    (contMDiff_iff_contDiff.mpr hu).contMDiffOn, ?_⟩
  intro s hs
  exact m64Intrinsic_geodesic_of_metric_germ G N.metric
    (fun t ht => hgeo s hs.2 t (hIJ ht)) (fun t ht => hmetric s hs.1 t ht)

end PoincareConjecture
