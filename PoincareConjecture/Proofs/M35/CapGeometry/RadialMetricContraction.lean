import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialMetric
import PoincareConjecture.Proofs.M35.CapGeometry.RadialEndSlope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)

include D hsec

theorem intrinsicWarpingRadius_le_self {s : ℝ} (hs : 0 ≤ s) :
    intrinsicWarpingRadius g hrotation hcomplete s ≤ s := by
  let f := intrinsicWarpingRadius g hrotation hcomplete
  have hanti : AntitoneOn (fun r => f r - r) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun r => axisWarpingSlope g
        ((radialArclengthOrderIso g hrotation hcomplete).symm r) - 1)
      (((intrinsicWarpingRadius_contDiff g hrotation hcomplete).continuous.sub
        continuous_id).continuousOn) ?_ ?_
    · intro r hr
      have hr' : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
      exact ((intrinsicWarpingRadius_hasDerivAt g hrotation hcomplete hr').sub
        (hasDerivAt_id r)).hasDerivWithinAt
    · intro r hr
      have hr' : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
      exact sub_nonpos.mpr (axisWarpingSlope_le_one D hrotation hsec
        (radialArclengthOrderIso_symm_pos g hrotation hcomplete hr'))
  have h := hanti (mem_Ici.mpr le_rfl) hs hs
  simpa only [f, intrinsicWarpingRadius_zero, zero_sub, neg_zero, sub_nonpos] using h

theorem intrinsicWarpingQuotient_le_one {s : ℝ} (hs : 0 ≤ s) :
    intrinsicWarpingQuotient g hrotation hcomplete s ≤ 1 := by
  rcases hs.eq_or_lt with rfl | hs'
  · rw [intrinsicWarpingQuotient_zero]
  · apply (mul_le_mul_iff_of_pos_left hs').mp
    rw [mul_intrinsicWarpingQuotient, mul_one]
    exact intrinsicWarpingRadius_le_self g D hrotation hcomplete hsec hs'.le

theorem intrinsicSpatialMetric_inner_le (x v : StandardCapSpace) :
    (intrinsicSpatialMetric g hrotation hcomplete).inner x v v ≤ inner ℝ v v := by
  by_cases hx : x = 0
  · subst x
    rw [intrinsicSpatialMetric_inner_zero]
  rw [intrinsicSpatialMetric_inner g hrotation hcomplete hx]
  let q := intrinsicWarpingQuotient g hrotation hcomplete ‖x‖
  have hq0 : 0 ≤ q := (intrinsicWarpingQuotient_pos g hrotation hcomplete _).le
  have hq1 : q ≤ 1 := intrinsicWarpingQuotient_le_one g D hrotation hcomplete hsec
    (norm_nonneg x)
  have hsq : q ^ 2 ≤ 1 := by nlinarith only [hq0, hq1]
  have hproj : inner ℝ x v * inner ℝ x v / ‖x‖ ^ 2 ≤ inner ℝ v v := by
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr
    simpa only [real_inner_self_eq_norm_sq, mul_comm] using real_inner_mul_inner_self_le x v
  have h := mul_le_mul_of_nonneg_left hproj (sub_nonneg.mpr hsq)
  change q ^ 2 * inner ℝ v v + (1 - q ^ 2) *
    (inner ℝ x v * inner ℝ x v) / ‖x‖ ^ 2 ≤ inner ℝ v v
  calc
    _ = q ^ 2 * inner ℝ v v + (1 - q ^ 2) *
        (inner ℝ x v * inner ℝ x v / ‖x‖ ^ 2) := by ring
    _ ≤ q ^ 2 * inner ℝ v v + (1 - q ^ 2) * inner ℝ v v := add_le_add_right h _
    _ = _ := by ring

theorem intrinsicSpatialInverse_tangentNorm_le (x v : StandardCapSpace) :
    g.tangentNorm (intrinsicSpatialInverse g hrotation hcomplete x)
      (mfderiv (𝓡 3) (𝓡 3) (intrinsicSpatialInverse g hrotation hcomplete) x v) ≤
        ‖v‖ := by
  calc
    _ = Real.sqrt ((intrinsicSpatialMetric g hrotation hcomplete).inner x v v) := by
      rw [RiemannianMetric.tangentNorm, mfderiv_eq_fderiv]
      convert! congrArg Real.sqrt (intrinsicSpatialMetric_pullback
        g hrotation hcomplete x v v).symm using 1
    _ ≤ Real.sqrt (inner ℝ v v) := Real.sqrt_le_sqrt
      (intrinsicSpatialMetric_inner_le g D hrotation hcomplete hsec x v)
    _ = ‖v‖ := by rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

end PoincareConjecture.M35.Uniqueness
