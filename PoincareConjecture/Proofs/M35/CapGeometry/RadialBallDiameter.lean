import PoincareConjecture.Proofs.M35.CapGeometry.RadialMetricContraction
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialDistance
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapDistance
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean
import Mathlib.Analysis.Calculus.Deriv.AffineMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace

variable (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : V,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)

private theorem line_contMDiff (x y : V) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (AffineMap.lineMap x y : ℝ → V) := by
  apply ContDiff.contMDiff
  change ContDiff ℝ ∞ (fun u : ℝ => u • (y - x) + x)
  exact (contDiff_id.smul contDiff_const).add contDiff_const

include D hsec in
theorem intrinsic_inverse_segment_length_le (x y : V) :
    g.pathELength (intrinsicSpatialInverse g hrotation hcomplete ∘
      (AffineMap.lineMap x y : ℝ → V)) 0 1 ≤ ENNReal.ofReal ‖y - x‖ := by
  let euc := RiemannianMetric.euclideanMetric 3
  let line : ℝ → V := AffineMap.lineMap x y
  have hd (u : ℝ) : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) line u 1 = y - x := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ line u (1 : ℝ) = y - x
    have h := (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := u)).hasFDerivAt
    rw [h.fderiv]
    exact one_smul ℝ (y - x)
  have hn (u : ℝ) : euc.tangentNorm (line u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) line u 1) = ‖y - x‖ := by
    change (RiemannianMetric.euclideanMetric 3).tangentNorm (line u) _ = _
    rw [RiemannianMetric.euclideanMetric_tangentNorm]
    exact congrArg norm (hd u)
  have hlength : euc.pathELength line 0 1 = ENNReal.ofReal ‖y - x‖ := by
    rw [M13.pathELength_eq_lintegral_tangentNorm]
    simp_rw [hn]
    simp
  have hbound := pathELength_comp_le_of_tangentNorm_le euc g
    (intrinsicSpatialInverse g hrotation hcomplete) isOpen_univ
    (intrinsicSpatialInverse_contDiff g hrotation hcomplete).contMDiff.contMDiffOn
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun z _ v => by
      change _ ≤ 1 * (RiemannianMetric.euclideanMetric 3).tangentNorm z v
      rw [one_mul, RiemannianMetric.euclideanMetric_tangentNorm]
      exact intrinsicSpatialInverse_tangentNorm_le g D hrotation hcomplete hsec z v)
    line 0 1 (line_contMDiff x y |>.of_le (by simp) |>.contMDiffOn)
    (fun _ _ => mem_univ _)
  simpa only [hlength, ENNReal.ofReal_one, one_mul] using hbound

include D hsec in

theorem intrinsicSpatialInverse_edist_le (x y : V) :
    g.edist (intrinsicSpatialInverse g hrotation hcomplete x)
      (intrinsicSpatialInverse g hrotation hcomplete y) ≤ edist x y := by
  have hs := (intrinsicSpatialInverse_contDiff g hrotation hcomplete).contMDiff.comp
    (line_contMDiff x y)
  have h := M13.edist_le_pathELength g
    (x := intrinsicSpatialInverse g hrotation hcomplete x)
    (y := intrinsicSpatialInverse g hrotation hcomplete y)
    (hs.of_le (by simp)).contMDiffOn
    (by simp only [Function.comp_apply, AffineMap.lineMap_apply_zero])
    (by simp only [Function.comp_apply, AffineMap.lineMap_apply_one])
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [edist_dist, dist_eq_norm, norm_sub_rev]
  exact h.trans (intrinsic_inverse_segment_length_le g D hrotation hcomplete hsec x y)

theorem intrinsicSpatialInverse_image_ball (P : M35StandardCapPredecessors) (R : ℝ) :
    intrinsicSpatialInverse g hrotation hcomplete '' Metric.ball (0 : V) R =
      g.ball 0 R := by
  have hpoint (u : V) : g.edist 0 (intrinsicSpatialInverse g hrotation hcomplete u) =
      ENNReal.ofReal ‖u‖ := by
    rw [edist_zero_eq_radialArclength g hrotation hcomplete P,
      ← intrinsicSpatialCoordinate_norm, intrinsicSpatialCoordinate_inverse]
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    change g.edist 0 (intrinsicSpatialInverse g hrotation hcomplete u) < ENNReal.ofReal R
    rw [hpoint, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg u)]
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  · intro hy
    refine ⟨intrinsicSpatialCoordinate g y, ?_,
      intrinsicSpatialInverse_coordinate g hrotation hcomplete y⟩
    have h := hpoint (intrinsicSpatialCoordinate g y)
    rw [intrinsicSpatialInverse_coordinate] at h
    change g.edist 0 y < ENNReal.ofReal R at hy
    rw [h, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)] at hy
    simpa only [Metric.mem_ball, dist_zero_right] using hy

include D hsec hrotation hcomplete in

theorem radial_ball_intrinsic_diameter (P : M35StandardCapPredecessors)
    {R : ℝ} {x y : V} (hx : x ∈ g.ball 0 R) (hy : y ∈ g.ball 0 R) :
    standardCapIntrinsicEDist g (g.ball 0 R) x y < ENNReal.ofReal (2 * R) := by
  rw [← intrinsicSpatialInverse_image_ball g hrotation hcomplete P R] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  let line : ℝ → V := AffineMap.lineMap u v
  let f := intrinsicSpatialInverse g hrotation hcomplete
  have hs := (intrinsicSpatialInverse_contDiff g hrotation hcomplete).contMDiff.comp
    (line_contMDiff u v)
  have hdist : standardCapIntrinsicEDist g (g.ball 0 R) (f u) (f v) ≤
      g.pathELength (f ∘ line) 0 1 := by
    apply sInf_le
    refine ⟨f ∘ line, (hs.of_le (by simp)).contMDiffOn,
      by simp [line], by simp [line], ?_, rfl⟩
    rintro z ⟨r, hr, rfl⟩
    rw [← intrinsicSpatialInverse_image_ball g hrotation hcomplete P R]
    exact ⟨line r, (convex_ball (0 : V) R).lineMap_mem hu hv hr, rfl⟩
  have huv : ‖v - u‖ < 2 * R := by
    have hu' : ‖u‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hv' : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    exact (norm_sub_le v u).trans_lt (by linarith only [hu', hv'])
  exact (hdist.trans (intrinsic_inverse_segment_length_le
    g D hrotation hcomplete hsec u v)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr huv)

end PoincareConjecture.M35.Uniqueness
