import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularExponential
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionMinimizer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CornerRigidity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_shortening_chord
    (N : IntrinsicAnnulus) (p : AnnulusCoordinates) {v w : AnnulusCoordinates}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hne : w ≠ -v) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (0 : AnnulusCoordinates) ∈ F.source ∧ F 0 = p ∧
      ContDiffOn ℝ ∞ F F.source ∧
      (∀ z ∈ F.source, N.metric.IsGeodesicOn (fun t : ℝ => F (t • z))
        {t : ℝ | t • z ∈ F.source}) ∧
      ∃ rho : ℝ, 0 < rho ∧ ∀ r : ℝ, 0 < r → r < rho →
        (∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap (r • v) (r • w) t ∈ F.source) ∧
        ContDiffOn ℝ ∞ (fun t : ℝ => F (AffineMap.lineMap (r • v) (r • w) t)) (Icc 0 1) ∧
        m64IntrinsicCurveVariation N.metric
          (fun t : ℝ => F (AffineMap.lineMap (r • v) (r • w) t)) 0 1 < ENNReal.ofReal (2 * r) := by
  have htheta : ∃ theta : ℝ, 1 < theta ∧ theta * ‖w - v‖ < 2 := by
    by_contra h
    push Not at h
    exact hne (eq_neg_of_norm_lower_bound hv hw h)
  obtain ⟨theta, htheta, htheta2⟩ := htheta
  let C : ℝ≥0 := ⟨theta, (zero_lt_one.trans htheta).le⟩
  obtain ⟨R, hR, e, he0, he, hmetric, _, hgeo, hinj, _⟩ :=
    m64Intrinsic_exists_regular_radial_exponential N p
  have hzero : (0 : AnnulusCoordinates) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  obtain ⟨F, hF0, hFU, hFe, hF, hFi⟩ :=
    m64Intrinsic_exists_smooth_polar_inverse Metric.isOpen_ball he hzero (hinj 0 hzero)
  have hFsm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source :=
    contMDiffOn_iff_contDiffOn.mpr hF
  have hFism : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target :=
    contMDiffOn_iff_contDiffOn.mpr hFi
  let A := ContinuousLinearEquiv.refl ℝ AnnulusCoordinates
  have hA (z : AnnulusCoordinates) :
      ‖A z‖ = N.metric.tangentNorm (F 0) (mfderiv (𝓡 2) (𝓡 2) F 0 z) := by
    change ‖z‖ = Real.sqrt (N.metric.inner (F 0)
      (mfderiv (𝓡 2) (𝓡 2) F 0 z) (mfderiv (𝓡 2) (𝓡 2) F 0 z))
    rw [hFe, hmetric]
    exact norm_eq_sqrt_real_inner z
  obtain ⟨U, hU, h0U, hUF, hdist⟩ := N.metric.exists_open_distortion_of_tangentNorm_comparison
    F hFsm hFism hF0 A (show 1 < C from htheta)
    (N.metric.eventually_pullbackNorm_comparison
      (hFsm.contMDiffAt (F.open_source.mem_nhds hF0)) A hA (show 1 < C from htheta))
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨F, hF0, by simpa only [hFe] using he0, hF, ?_, rho, hrho, ?_⟩
  · intro z hz t ht
    rw [hFe]
    exact hgeo z (hFU hz) t (hFU ht)
  · intro r hr hrrho
    have hvball : r • v ∈ Metric.ball (0 : AnnulusCoordinates) rho := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hv, mul_one] using hrrho
    have hwball : r • w ∈ Metric.ball (0 : AnnulusCoordinates) rho := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hw, mul_one] using hrrho
    have hline (t : ℝ) (ht : t ∈ Icc 0 1) :
        AffineMap.lineMap (r • v) (r • w) t ∈ U :=
      hball ((convex_ball (0 : AnnulusCoordinates) rho).lineMap_mem hvball hwball ht)
    have hsource : MapsTo (AffineMap.lineMap (r • v) (r • w)) (Icc (0 : ℝ) 1) F.source :=
      fun t ht => hUF (hline t ht)
    refine ⟨fun t ht => hsource ht, hF.comp (by fun_prop) hsource, ?_⟩
    have hlength := m64Intrinsic_curveVariation_le_of_edist_le N.metric
      (C := theta * r * ‖w - v‖) (by positivity) (by
        intro s hs t ht
        have h := (hdist _ (hline s hs) _ (hline t ht)).1
        change N.metric.edist (F (AffineMap.lineMap (r • v) (r • w) s))
          (F (AffineMap.lineMap (r • v) (r • w) t)) ≤
          (C : ℝ≥0∞) * edist (AffineMap.lineMap (r • v) (r • w) s)
            (AffineMap.lineMap (r • v) (r • w) t) at h
        rw [edist_dist, dist_lineMap_lineMap, Real.dist_eq, dist_eq_norm', ← smul_sub,
          norm_smul, Real.norm_eq_abs, abs_of_pos hr,
          ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at h
        convert h using 1
        congr 1
        change theta * r * ‖w - v‖ * |s - t| = theta * (|s - t| * (r * ‖w - v‖))
        ring)
    apply hlength.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * r)).mpr
    nlinarith [mul_lt_mul_of_pos_right htheta2 hr]

end PoincareConjecture
