import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalRays
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

theorem m64Intrinsic_exists_uniformly_positive_extension (N : IntrinsicAnnulus) :
    ∃ (G : RiemannianMetric 2 AnnulusCoordinates) (c : ℝ), 0 < c ∧
      (∀ p ∈ standardAnnulusDomain,
        G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients) ∧
      (∀ p v : AnnulusCoordinates, c * ‖v‖ ≤ G.tangentNorm p v) ∧
      ∀ p : AnnulusCoordinates, 4 ≤ ‖p‖ → G.euclideanCoefficients p = innerSL ℝ := by
  let f : ContDiffBump (0 : AnnulusCoordinates) := ⟨3, 4, by norm_num, by norm_num⟩
  let E : AnnulusCoordinates →L[ℝ] AnnulusCoordinates →L[ℝ] ℝ := innerSL ℝ
  let B : AnnulusCoordinates → AnnulusCoordinates →L[ℝ] AnnulusCoordinates →L[ℝ] ℝ :=
    fun p => f p • N.metric.euclideanCoefficients p + (1 - f p) • E
  have hB : ContDiff ℝ ∞ B := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (f.contDiffAt.smul (N.metric.contDiffAt_euclideanCoefficients p)).add
      ((contDiffAt_const.sub f.contDiffAt).smul contDiffAt_const)
  have hBa (p v w : AnnulusCoordinates) :
      B p v w = f p * N.metric.inner p v w + (1 - f p) * inner ℝ v w := rfl
  have hsymm (p v w : AnnulusCoordinates) : B p v w = B p w v := by
    rw [hBa, hBa, N.metric.symm, real_inner_comm v w]
  have hpos (p v : AnnulusCoordinates) (hv : v ≠ 0) : 0 < B p v v := by
    rw [hBa]
    by_cases hfp : f p = 0
    · simpa only [hfp, zero_mul, sub_zero, one_mul, zero_add] using
        real_inner_self_pos.mpr hv
    · have hfpos : 0 < f p := lt_of_le_of_ne f.nonneg (Ne.symm hfp)
      exact add_pos_of_pos_of_nonneg (mul_pos hfpos (N.metric.pos p v hv))
        (mul_nonneg (sub_nonneg.mpr f.le_one) real_inner_self_nonneg)
  let G := RiemannianMetric.ofEuclideanCoefficients B hB hsymm hpos
  have hGcoeff : G.euclideanCoefficients = B := rfl
  have heq (p : AnnulusCoordinates) (hp : p ∈ Metric.ball 0 3) :
      G.euclideanCoefficients p = N.metric.euclideanCoefficients p := by
    have hfp : f p = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall.mpr
      (Metric.mem_ball.mp hp).le)
    ext v w
    change B p v w = N.metric.inner p v w
    rw [hBa, hfp]
    ring
  have houtside (p : AnnulusCoordinates) (hp : 4 ≤ ‖p‖) :
      G.euclideanCoefficients p = innerSL ℝ := by
    have hfp : f p = 0 := f.zero_of_le_dist (by simpa only [dist_zero_right] using hp)
    ext v w
    change B p v w = inner ℝ v w
    rw [hBa, hfp]
    ring
  obtain ⟨d, hd, hlower⟩ := exists_uniform_bilinear_lower_bound
    (isCompact_closedBall (0 : AnnulusCoordinates) 4) hB.continuous.continuousOn
      (fun p _ v hv => hpos p v hv)
  let c := min d 1
  have hc : 0 < c := lt_min hd zero_lt_one
  have hglobal (p v : AnnulusCoordinates) : c * ‖v‖ ^ 2 ≤ G.inner p v v := by
    by_cases hp : ‖p‖ ≤ 4
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖v‖)).trans
        (hlower p (by simpa only [Metric.mem_closedBall, dist_zero_right] using hp) v)
    · have hg := congrArg (fun A : AnnulusCoordinates →L[ℝ]
          AnnulusCoordinates →L[ℝ] ℝ => A v v) (houtside p (le_of_not_ge hp))
      change G.inner p v v = inner ℝ v v at hg
      rw [hg, real_inner_self_eq_norm_sq]
      exact mul_le_of_le_one_left (sq_nonneg ‖v‖) (min_le_right _ _)
  refine ⟨G, Real.sqrt c, Real.sqrt_pos.mpr hc, ?_, ?_, houtside⟩
  · intro p hp
    have hpball : p ∈ Metric.ball (0 : AnnulusCoordinates) 3 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hp.2.trans_lt (by norm_num)
    filter_upwards [Metric.isOpen_ball.mem_nhds hpball] with x hx
    exact heq x hx
  · intro p v
    have hnonneg : 0 ≤ G.inner p v v := (mul_nonneg hc.le (sq_nonneg ‖v‖)).trans
      (hglobal p v)
    have hs := Real.sq_sqrt hnonneg
    have hc2 := Real.sq_sqrt hc.le
    change Real.sqrt c * ‖v‖ ≤ Real.sqrt (G.inner p v v)
    nlinarith [hglobal p v, Real.sqrt_nonneg c, Real.sqrt_nonneg (G.inner p v v),
      mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg v)]

end PoincareConjecture
