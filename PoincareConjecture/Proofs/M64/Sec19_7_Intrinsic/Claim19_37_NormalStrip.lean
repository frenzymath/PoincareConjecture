import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalDomain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_ContactTime
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_UniformMetric















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_normal_endpoint_initial_data
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hend : ∀ z : ℝ × ℝ, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ gamma : ℝ → AnnulusCoordinates,
        G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
        gamma 0 = intrinsicAnnulusBoundary 1 z.1 ∧
        HasDerivAt gamma (z.2 • normal z.1) 0 ∧ gamma 1 = u z)
    (a : ℝ) :
    u (a, 0) = intrinsicAnnulusBoundary 1 a ∧
      HasDerivAt (fun t => u (a, t)) (normal a) 0 := by
  obtain ⟨epsilon, hepsilon, gamma, hgamma, hinit, hderiv, _⟩ := hend (a, 1)
  have hderiv' : HasDerivAt gamma (normal a) 0 := by
    simpa only [one_smul] using hderiv
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) (1 + epsilon) := ⟨by linarith, by linarith⟩
  have hgerm : (fun t => u (a, t)) =ᶠ[𝓝 0] gamma := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with t ht
    exact m64Intrinsic_normal_endpoint_eq_geodesic G hend hzero hgamma hinit hderiv' ht
  exact ⟨hgerm.self_of_nhds.trans hinit, hderiv'.congr_of_eventuallyEq hgerm⟩






theorem m64Intrinsic_exists_uniform_normal_strip
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
        ∃ (normal : ℝ → AnnulusCoordinates) (u : ℝ × ℝ → AnnulusCoordinates),
          ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
          (∀ s, N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s) (normal s) = 1 ∧
            N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s)
              (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) s) = 0 ∧
            0 < inner ℝ (intrinsicAnnulusBoundary 1 s) (normal s)) ∧
          (∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
          (∀ s, HasDerivAt (fun t => u (s, t)) (normal s) 0) ∧
          ∀ a : ℝ, intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
            ∃ (b : ℝ) (S I : Set ℝ), 0 < b ∧ b ≤ R ∧ IsOpen S ∧ IsOpen I ∧
              a ∈ S ∧ Icc (0 : ℝ) b ⊆ I ∧
              (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) ∧
              (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) ∧
              u (a, b) ∈ standardAnnulusDomain ∧
              (b = R ∨ ‖u (a, b)‖ = 1 ∨ ‖u (a, b)‖ = 2) ∧
              ∀ t ∈ Icc (0 : ℝ) b,
                (∀ v : ℝ × ℝ,
                  (1 - delta) ^ 2 *
                    ((intrinsicBoundarySpeed N.metric 1 a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
                    N.metric.inner (u (a, t))
                      (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
                Function.Injective (fderiv ℝ u (a, t)) := by
  obtain ⟨R, hR, hRsmall, hmetric⟩ :=
    m64Intrinsic_exists_uniform_normal_metric_radius K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro N hK
  obtain ⟨G, normal, u, hG, hnormal, hu, hn, hend⟩ :=
    m64Intrinsic_exists_smooth_extended_normal_endpoint N
  have hdata := m64Intrinsic_normal_endpoint_initial_data G hend
  refine ⟨normal, u, hnormal, hu, hn, fun a => (hdata a).1,
    fun a => (hdata a).2, ?_⟩
  intro a hturn
  obtain ⟨eta, heta, henter⟩ :=
    m64Intrinsic_inward_curve_enters_annulus (hdata a).1 (hdata a).2 (hn a).2.2
  have hcurve : Continuous (fun t => u (a, t)) :=
    hu.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨b, hb, hbR, hinside, hlast, hcontact⟩ :=
    m64Intrinsic_exists_first_annulus_contact hcurve hR heta henter
  have himage : ∀ t ∈ Icc (0 : ℝ) b, u (a, t) ∈ standardAnnulusDomain := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · rw [← hzero, (hdata a).1]
      have hnorm : ‖intrinsicAnnulusBoundary 1 a‖ = 1 := by
        have hsq := m64Intrinsic_boundary_self_inner 1 a
        rw [real_inner_self_eq_norm_sq] at hsq
        nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 a)]
      exact ⟨by rw [hnorm], by simpa only [hnorm] using (by norm_num : (1 : ℝ) ≤ 2)⟩
    · rcases eq_or_lt_of_le ht.2 with hlastTime | hlt
      · simpa only [hlastTime] using hlast
      · exact ⟨(hinside t ⟨hpos, hlt⟩).1.le, (hinside t ⟨hpos, hlt⟩).2.le⟩
  obtain ⟨S, I, hS, hI, ha, hsub, hsmooth, hgeo⟩ :=
    m64Intrinsic_exists_actual_normal_geodesic_neighborhood N G hG hnormal hu hend
      (show b < 1 by linarith) himage
  refine ⟨b, S, I, hb, hbR, hS, hI, ha, hsub, hgeo, hinside, hlast, hcontact, ?_⟩
  apply hmetric b hb hbR N 1 (by norm_num) hK u S I hS hI hsub hsmooth hgeo
    (fun s _ => (hdata s).1) normal hnormal (fun s => (hn s).1)
    (fun s => (hn s).2.1) ?_ a ha hturn
    (fun t ht => ⟨(hinside t ht).1.le, (hinside t ht).2.le⟩)
  intro s _
  rw [m64Intrinsic_curveVelocity_eq_deriv, (hdata s).2.deriv]

end PoincareConjecture
