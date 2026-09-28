import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MetricGerm
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularExponential
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialGeodesicRealization















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_isOpen_radial_core {V : Set AnnulusCoordinates} (hV : IsOpen V) :
    IsOpen {v : AnnulusCoordinates | ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ V} := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  let Omega : Set (AnnulusCoordinates × ℝ) := {z | z.2 • z.1 ∈ V}
  have hOmega : IsOpen Omega := hV.preimage (by fun_prop)
  have hsub : ({v} : Set AnnulusCoordinates) ×ˢ Icc (0 : ℝ) 1 ⊆ Omega := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    have hwv : w = v := mem_singleton_iff.mp hw
    simpa only [Omega, mem_ofPred_eq, hwv] using hv t ht
  obtain ⟨S, I, hS, _, hvS, hI, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hOmega hsub
  apply Filter.mem_of_superset (hS.mem_nhds (hvS (mem_singleton v)))
  intro w hw t ht
  exact hprod (show (w, t) ∈ S ×ˢ I from ⟨hw, hI ht⟩)





theorem m64Intrinsic_exists_continued_radial_exponential_realizing_geodesics
    (N : IntrinsicAnnulus) {p : AnnulusCoordinates} (hp : p ∈ standardAnnulusDomain)
    {R : ℝ} (hR : 0 < R) :
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (U : Set AnnulusCoordinates),
      IsOpen U ∧ (0 : AnnulusCoordinates) ∈ U ∧ U ⊆ Metric.ball 0 R ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e (Metric.ball 0 R) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ U, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ U, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ U}) ∧
      (∀ v ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ U) ∧
      (∀ v ∈ Metric.ball 0 R,
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) → v ∈ U) ∧
      ∀ q : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ q →
        ∀ T : ℝ, 0 < T → T < R → q 0 = p →
          N.metric.IsGeodesicOn q (Icc 0 T) → MapsTo q (Icc 0 T) standardAnnulusDomain →
            N.metric.inner (q 0) (deriv q 0) (deriv q 0) = 1 →
              ∃ v : AnnulusCoordinates, v ∈ U ∧ ‖v‖ = T ∧
                ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = q (T * t) := by
  obtain ⟨G, c, hc, heq, hlower, _⟩ := m64Intrinsic_exists_uniformly_positive_extension N
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    G.exists_orthonormal_radial_exponential_of_precompact_ball p hR
      (m64Intrinsic_isCompact_closure_ball_of_uniform_lower G hc hlower p hR)
  let V := Metric.ball (0 : AnnulusCoordinates) R ∩
    e ⁻¹' {q | G.euclideanCoefficients =ᶠ[𝓝 q] N.metric.euclideanCoefficients}
  let U : Set AnnulusCoordinates := {v | ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ V}
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage Metric.isOpen_ball
    (m64Intrinsic_isOpen_metric_agreement G N.metric)
  have hU : IsOpen U := m64Intrinsic_isOpen_radial_core hV
  have hzero : (0 : AnnulusCoordinates) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have hzeroU : (0 : AnnulusCoordinates) ∈ U := by
    intro t _
    simpa only [smul_zero, V, mem_inter_iff, mem_preimage, mem_ofPred_eq, he0] using
      And.intro hzero (heq p hp)
  have hUV : U ⊆ V := fun v hv => by simpa only [one_smul] using hv 1 (by norm_num)
  have hball : U ⊆ Metric.ball 0 R := fun _ hv => (hUV hv).1
  have hpoint (v : AnnulusCoordinates) (hv : v ∈ U) :
      G.euclideanCoefficients (e v) = N.metric.euclideanCoefficients (e v) :=
    (hUV hv).2.self_of_nhds
  refine ⟨e, U, hU, hzeroU, hball, he0, he, he.mono hball, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w
    have hm := G.pullbackCoefficients_zero_of_orthonormal p
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hzero)) he0 hed hL v w
    have h0metric := hpoint 0 hzeroU
    change G.inner (e 0) = N.metric.inner (e 0) at h0metric
    rw [← h0metric]
    exact hm
  · intro v hv w
    have hg := CoordinateExponential.gauss_identity_of_radial_family G he
      (fun z hz => (hgeo z hz).1)
      (fun z hz t ht => ((hgeo z hz).2 t ht).1) v (hball hv) w
    have hmetric := hpoint v hv
    change G.inner (e v) = N.metric.inner (e v) at hmetric
    change N.metric.inner (e v) (mfderiv (𝓡 2) (𝓡 2) e v v)
      (mfderiv (𝓡 2) (𝓡 2) e v w) = _
    rw [← hmetric]
    exact hg
  · intro v hv
    apply m64Intrinsic_geodesic_of_metric_germ G N.metric
      (fun t ht => (hgeo v (hball hv)).1 t (hball ht))
    intro t ht
    exact (hUV ht).2
  · intro v hv t ht s hs
    have hst : s * t ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hs.1 ht.1, (mul_le_mul hs.2 ht.2 ht.1 zero_le_one).trans (by norm_num)⟩
    simpa only [smul_smul] using hv (s * t) hst
  · intro v hv hmap t ht
    refine ⟨?_, heq _ (hmap t ht)⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt
      (by simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hv)
  · intro q hq T hT hTR hq0 hqgeo hqconf hqunit
    have hGgeo := m64Intrinsic_geodesic_of_metric_germ N.metric G hqgeo
      (fun t ht => (heq (q t) (hqconf ht)).symm)
    have hGunit : G.inner (q 0) (deriv q 0) (deriv q 0) = 1 := by
      have hm := (heq (q 0) (hqconf ⟨le_rfl, hT.le⟩)).self_of_nhds
      change G.inner (q 0) = N.metric.inner (q 0) at hm
      rw [hm]
      exact hqunit
    have hL' : ∀ v w, G.inner p (L v) (L w) = inner ℝ v w := by
      intro v w
      have hh := hL v w
      change G.pullbackCoefficients (extChartAt (𝓡 2) p).symm
        (extChartAt (𝓡 2) p p) (L v) (L w) = inner ℝ v w at hh
      rw [m64Intrinsic_model_chart_coefficients] at hh
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq,
        RiemannianMetric.euclideanCoefficients] using! hh
    have hed' : HasFDerivAt e L.toContinuousLinearMap 0 := by
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using hed
    obtain ⟨v, hnorm, hv, hreadout⟩ := m64Intrinsic_unit_geodesic_radial_realization
      G L hL' he0 hed' (fun z hz => (hgeo z hz).1) hq hT hTR hq0 hGgeo hGunit
    refine ⟨v, ?_, hnorm, hreadout⟩
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt
        (by simpa only [one_mul, hnorm] using hTR)
    · apply heq
      rw [hreadout t ht]
      exact hqconf ⟨mul_nonneg hT.le ht.1,
        (mul_le_mul_of_nonneg_left ht.2 hT.le).trans_eq (mul_one T)⟩





theorem m64Intrinsic_exists_continued_radial_exponential_on_ball
    (N : IntrinsicAnnulus) {p : AnnulusCoordinates} (hp : p ∈ standardAnnulusDomain)
    {R : ℝ} (hR : 0 < R) :
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (U : Set AnnulusCoordinates),
      IsOpen U ∧ (0 : AnnulusCoordinates) ∈ U ∧ U ⊆ Metric.ball 0 R ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e (Metric.ball 0 R) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ U, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ U, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ U}) ∧
      (∀ v ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ U) ∧
      ∀ v ∈ Metric.ball 0 R,
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) → v ∈ U := by
  obtain ⟨e, U, hU, hzero, hball, he0, hes, he, hm, hg, hgeo, hstar, hcontains, _⟩ :=
    m64Intrinsic_exists_continued_radial_exponential_realizing_geodesics N hp hR
  exact ⟨e, U, hU, hzero, hball, he0, hes, he, hm, hg, hgeo, hstar, hcontains⟩






theorem m64Intrinsic_exists_continued_radial_exponential
    (N : IntrinsicAnnulus) {p : AnnulusCoordinates} (hp : p ∈ standardAnnulusDomain)
    {R : ℝ} (hR : 0 < R) :
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (U : Set AnnulusCoordinates),
      IsOpen U ∧ (0 : AnnulusCoordinates) ∈ U ∧ U ⊆ Metric.ball 0 R ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ U, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ U, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ U}) ∧
      (∀ v ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ U) ∧
      ∀ v ∈ Metric.ball 0 R,
        (∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ standardAnnulusDomain) → v ∈ U := by
  obtain ⟨e, U, hU, hzero, hball, he0, _, he, hmetric, hgauss, hgeo, hstar, hcontains⟩ :=
    m64Intrinsic_exists_continued_radial_exponential_on_ball N hp hR
  exact ⟨e, U, hU, hzero, hball, he0, he, hmetric, hgauss, hgeo, hstar, hcontains⟩

end PoincareConjecture
