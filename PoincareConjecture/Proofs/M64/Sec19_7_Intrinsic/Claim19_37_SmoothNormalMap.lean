import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_SmoothEndpoint
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open RiemannianMetric

theorem m64Intrinsic_normal_endpoint_eq_geodesic
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
    (hderiv : HasDerivAt gamma (normal a) 0) {t : ℝ} (ht : t ∈ Ioo lo hi) :
    u (a, t) = gamma t := by
  obtain ⟨epsilon, hepsilon, eta, heta, heta0, hetad, heta1⟩ := hend (a, t)
  have hscale : G.IsGeodesicOn (fun s => gamma (t * s)) (Icc (0 : ℝ) 1) := by
    intro s hs
    apply hgamma.comp_mul t s
    have hm : (1 - s) • (0 : ℝ) + s • t ∈ Ioo lo hi :=
      (convex_Ioo lo hi) hzero ht (sub_nonneg.mpr hs.2) hs.1 (by ring)
    change (1 - s) * 0 + s * t ∈ Ioo lo hi at hm
    simp only [mul_zero, zero_add] at hm
    change t * s ∈ Ioo lo hi
    simpa only [mul_comm] using hm
  have heta' : G.IsGeodesicOn eta (Icc (0 : ℝ) 1) := by
    intro s hs
    exact heta s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hd : HasDerivAt (fun s => gamma (t * s)) (t • normal a) 0 := by
    have hd' : HasDerivAt gamma (normal a) (t * 0) := by
      simpa only [mul_zero] using hderiv
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hd'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t)
  have hvel : deriv (fun s => extChartAt (𝓡 2)
      (intrinsicAnnulusBoundary 1 a) (gamma (t * s))) 0 =
      deriv (fun s => extChartAt (𝓡 2) (intrinsicAnnulusBoundary 1 a) (eta s)) 0 := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
      hd.deriv.trans hetad.deriv.symm
  have heq := hscale.eq_nhds_on_of_initial_data heta' (convex_Icc _ _).isPreconnected
    (t₀ := 0) (by simp) (intrinsicAnnulusBoundary 1 a)
    (by simp) (by simpa only [mul_zero, hinit] using heta0.symm) hvel
  simpa only [mul_one, heta1] using (heq 1 (by simp)).self_of_nhds.symm

theorem m64Intrinsic_exists_smooth_extended_normal_map (N : IntrinsicAnnulus) :
    ∃ (G : RiemannianMetric 2 AnnulusCoordinates)
      (normal : ℝ → AnnulusCoordinates) (u : ℝ × ℝ → AnnulusCoordinates),
      (∀ p ∈ standardAnnulusDomain,
        G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients) ∧
      ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      (∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0) ∧
      ∀ a, G.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) 1) := by
  obtain ⟨G, normal, u, hG, hnormal, hu, hn, hend⟩ :=
    m64Intrinsic_exists_smooth_extended_normal_endpoint N
  have hdata (a : ℝ) :
      u (a, 0) = intrinsicAnnulusBoundary 1 a ∧
      HasDerivAt (fun t => u (a, t)) (normal a) 0 ∧
      G.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) 1) := by
    obtain ⟨epsilon, hepsilon, gamma, hgamma, hinit, hderiv, _⟩ := hend (a, 1)
    have hderiv' : HasDerivAt gamma (normal a) 0 := by
      simpa only [one_smul] using hderiv
    have hzero : (0 : ℝ) ∈ Ioo (-epsilon) (1 + epsilon) := ⟨by linarith, by linarith⟩
    have heq : EqOn (fun t => u (a, t)) gamma (Ioo (-epsilon) (1 + epsilon)) :=
      fun _ ht => m64Intrinsic_normal_endpoint_eq_geodesic G hend hzero hgamma hinit hderiv' ht
    have hgerm {t : ℝ} (ht : t ∈ Ioo (-epsilon) (1 + epsilon)) :
        (fun r => u (a, r)) =ᶠ[𝓝 t] gamma := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact heq hr
    refine ⟨(heq hzero).trans hinit, hderiv'.congr_of_eventuallyEq (hgerm hzero), ?_⟩
    intro t ht
    have ht' : t ∈ Ioo (-epsilon) (1 + epsilon) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨p, q, w, hlocal⟩ := hgamma t ht'
    refine ⟨p, q, w, ?_⟩
    filter_upwards [hlocal, hgerm ht'] with r hr her
    exact ⟨her.trans hr.1, hr.2⟩
  exact ⟨G, normal, u, hG, hnormal, hu, hn, fun a => (hdata a).1,
    fun a => (hdata a).2.1, fun a => (hdata a).2.2⟩

end PoincareConjecture
