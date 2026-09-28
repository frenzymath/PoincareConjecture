import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ShorteningChord
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_tangentNorm_sub_lt_two
    (G : RiemannianMetric 2 AnnulusCoordinates) (p : AnnulusCoordinates)
    {v w : TangentSpace (𝓡 2) p}
    (hv : G.tangentNorm p v = 1) (hw : G.tangentNorm p w = 1)
    (hne : w ≠ -v) : G.tangentNorm p (w - v) < 2 := by
  obtain ⟨L, hL⟩ := G.exists_orthonormal_coordinate_frame p
  have hnorm (z : TangentSpace (𝓡 2) p) : G.tangentNorm p z = ‖L.symm z‖ := by
    unfold RiemannianMetric.tangentNorm
    rw [← L.apply_symm_apply z, ← G.chartCoefficients_center,
      hL, ← norm_eq_sqrt_real_inner]
    simp only [L.symm_apply_apply]
  have hne' : L.symm w ≠ -L.symm v := by
    intro h
    apply hne
    simpa only [map_neg, L.apply_symm_apply] using congrArg L h
  have htheta : ∃ theta : ℝ, 1 < theta ∧ theta * ‖L.symm w - L.symm v‖ < 2 := by
    by_contra h
    push Not at h
    exact hne' (eq_neg_of_norm_lower_bound (by simpa only [hnorm] using hv)
      (by simpa only [hnorm] using hw) h)
  obtain ⟨theta, htheta, htheta2⟩ := htheta
  rw [hnorm, map_sub]
  nlinarith [norm_nonneg (L.symm w - L.symm v)]

theorem m64Intrinsic_exists_short_corner_sector_curve
    (N : IntrinsicAnnulus)
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (h0 : (0 : AnnulusCoordinates) ∈ H.source)
    (hH : ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source)
    (v w : AnnulusCoordinates)
    (hv : N.metric.tangentNorm (H 0) (mfderiv (𝓡 2) (𝓡 2) H 0 v) = 1)
    (hw : N.metric.tangentNorm (H 0) (mfderiv (𝓡 2) (𝓡 2) H 0 w) = 1)
    (hne : mfderiv (𝓡 2) (𝓡 2) H 0 w ≠ -mfderiv (𝓡 2) (𝓡 2) H 0 v) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ r : ℝ, 0 < r → r < rho →
      ∃ σ : ℝ → AnnulusCoordinates,
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ σ (Icc 0 1) ∧
        σ 0 = H (r • v) ∧ σ 1 = H (r • w) ∧
        MapsTo σ (Icc 0 1)
          (H '' (H.source ∩ {z | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ z = a • v + b • w})) ∧
        m64IntrinsicCurveVariation N.metric σ 0 1 < ENNReal.ofReal (2 * r) := by
  let D := mfderiv (𝓡 2) (𝓡 2) H 0
  let speed (z : AnnulusCoordinates) :=
    Real.sqrt (N.metric.pullbackCoefficients H z (w - v) (w - v))
  have hspeed : speed 0 < 2 := by
    change N.metric.tangentNorm (H 0) (D (w - v)) < 2
    rw [map_sub]
    exact m64Intrinsic_tangentNorm_sub_lt_two N.metric (H 0) hv hw hne
  let c := (speed 0 + 2) / 2
  have hsc : speed 0 < c := by dsimp [c]; linarith
  have hc2 : c < 2 := by dsimp [c]; linarith
  have hspeedc : ContinuousAt speed 0 :=
    (((N.metric.contDiffAt_pullbackCoefficients
      (hH.contMDiffAt (H.open_source.mem_nhds h0))).continuousAt.clm_apply
        continuousAt_const).clm_apply continuousAt_const).sqrt
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (H.open_source.mem_nhds h0) (hspeedc.eventually (gt_mem_nhds hsc)))
  let M := max ‖v‖ ‖w‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨epsilon / M, div_pos hepsilon hM, ?_⟩
  intro r hr hrrho
  have hrM : r * M < epsilon := (lt_div_iff₀ hM).mp hrrho
  have hvball : r • v ∈ Metric.ball (0 : AnnulusCoordinates) epsilon := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (by dsimp [M]; linarith [le_max_left ‖v‖ ‖w‖])
      hr.le).trans_lt hrM
  have hwball : r • w ∈ Metric.ball (0 : AnnulusCoordinates) epsilon := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (by dsimp [M]; linarith [le_max_right ‖v‖ ‖w‖])
      hr.le).trans_lt hrM
  let q : ℝ → AnnulusCoordinates := AffineMap.lineMap (r • v) (r • w)
  have hqball (t : ℝ) (ht : t ∈ Icc 0 1) : q t ∈ Metric.ball 0 epsilon :=
    (convex_ball (0 : AnnulusCoordinates) epsilon).lineMap_mem hvball hwball ht
  have hqsource : MapsTo q (Icc 0 1) H.source := fun t ht => (hball (hqball t ht)).1
  have hqsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ q :=
    contMDiff_iff_contDiff.mpr (by dsimp [q]; fun_prop)
  have hsm := hH.comp hqsm.contMDiffOn hqsource
  refine ⟨H ∘ q, hsm, by simp [q], by simp [q], ?_, ?_⟩
  · intro t ht
    refine ⟨q t, ⟨hqsource ht, (1 - t) * r, t * r,
      mul_nonneg (sub_nonneg.mpr ht.2) hr.le, mul_nonneg ht.1 hr.le, ?_⟩, rfl⟩
    simp only [q, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  · have hlength : N.metric.pathELength (H ∘ q) 0 1 ≤ ENNReal.ofReal (r * c) := by
      rw [N.metric.pathELength_eq_lintegral_tangentNorm]
      calc
        _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (r * c) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro t ht
          have hqd : HasDerivAt q (r • (w - v)) t := by
            simpa only [q, smul_sub] using
              (AffineMap.hasDerivAt_lineMap (a := r • v) (b := r • w) (x := t))
          have hchain := mfderiv_comp t
            ((hH.contMDiffAt (H.open_source.mem_nhds (hqsource ht))).mdifferentiableAt
              (by simp)) (hqsm.mdifferentiable (by simp) t)
          have hdq : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1 = r • (w - v) := by
            rw [mfderiv_eq_fderiv]
            exact hqd.deriv
          have hvel : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (H ∘ q) t 1 =
              r • (mfderiv (𝓡 2) (𝓡 2) H (q t) (w - v)) := by
            have h := congrArg (fun A => A 1) hchain
            change _ = mfderiv (𝓡 2) (𝓡 2) H (q t)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1) at h
            rw [hdq, map_smul] at h
            exact h
          apply ENNReal.ofReal_le_ofReal
          rw [hvel, m64Intrinsic_tangentNorm_smul, abs_of_pos hr]
          exact mul_le_mul_of_nonneg_left (hball (hqball t ht)).2.le hr.le
        _ = ENNReal.ofReal (r * c) := by simp
    apply (m64Intrinsic_curveVariation_le_pathELength N.metric (hsm.of_le (by simp))).trans_lt
    apply hlength.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * r)).mpr
    nlinarith [mul_lt_mul_of_pos_left hc2 hr]

end PoincareConjecture
