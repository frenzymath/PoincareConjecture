import PoincareConjecture.Proofs.M35.CapGeometry.RadialMetricContraction
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialVariation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace

variable (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : V,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)

include D hsec



theorem intrinsicWarpingQuotient_lower_on_ball {R m s : ℝ}
    (hR : 0 < R) (hm : m ≤ intrinsicWarpingRadius g hrotation hcomplete R / R)
    (hs : 0 ≤ s) (hsR : s ≤ R) :
    m ≤ intrinsicWarpingQuotient g hrotation hcomplete s := by
  rcases hs.eq_or_lt with rfl | hs'
  · rw [intrinsicWarpingQuotient_zero]
    exact hm.trans ((div_le_one hR).mpr
      (intrinsicWarpingRadius_le_self g D hrotation hcomplete hsec hR.le))
  · have h := intrinsicWarpingRadius_ratio_antitoneOn g hrotation hcomplete D hsec
      hs' hR hsR
    have heq : intrinsicWarpingQuotient g hrotation hcomplete s =
        intrinsicWarpingRadius g hrotation hcomplete s / s := by
      apply (eq_div_iff hs'.ne').mpr
      simpa only [mul_comm] using mul_intrinsicWarpingQuotient g hrotation hcomplete s
    rw [heq]
    exact hm.trans h



theorem intrinsicSpatialMetric_inner_lower {R m : ℝ} (hR : 0 < R) (hm0 : 0 ≤ m)
    (hm : m ≤ intrinsicWarpingRadius g hrotation hcomplete R / R)
    {x : V} (hxR : ‖x‖ ≤ R) (v : V) :
    m ^ 2 * inner ℝ v v ≤ (intrinsicSpatialMetric g hrotation hcomplete).inner x v v := by
  let q := intrinsicWarpingQuotient g hrotation hcomplete ‖x‖
  have hmq : m ≤ q := intrinsicWarpingQuotient_lower_on_ball
    g D hrotation hcomplete hsec hR hm (norm_nonneg x) hxR
  have hq0 : 0 ≤ q := (intrinsicWarpingQuotient_pos g hrotation hcomplete _).le
  have hq1 : q ≤ 1 := intrinsicWarpingQuotient_le_one
    g D hrotation hcomplete hsec (norm_nonneg x)
  have hmsq : m ^ 2 ≤ q ^ 2 := by nlinarith only [hm0, hmq, hq0]
  have hqsq : q ^ 2 ≤ 1 := by nlinarith only [hq0, hq1]
  have hself : 0 ≤ inner ℝ v v := real_inner_self_nonneg
  by_cases hx : x = 0
  · subst x
    rw [intrinsicSpatialMetric_inner_zero]
    have hq : q = 1 := by simp only [q, norm_zero, intrinsicWarpingQuotient_zero]
    rw [hq, one_pow] at hmsq
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmsq hself
  · rw [intrinsicSpatialMetric_inner g hrotation hcomplete hx]
    have hproj : 0 ≤ (1 - q ^ 2) * (inner ℝ x v * inner ℝ x v) / ‖x‖ ^ 2 :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hqsq) (mul_self_nonneg _)) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right hmsq hself).trans (le_add_of_nonneg_right hproj)



theorem intrinsicSpatialInverse_tangentNorm_lower {R m : ℝ}
    (hR : 0 < R) (hm0 : 0 ≤ m)
    (hm : m ≤ intrinsicWarpingRadius g hrotation hcomplete R / R)
    {x : V} (hxR : ‖x‖ ≤ R) (v : V) :
    m * ‖v‖ ≤ g.tangentNorm (intrinsicSpatialInverse g hrotation hcomplete x)
      (mfderiv (𝓡 3) (𝓡 3) (intrinsicSpatialInverse g hrotation hcomplete) x v) := by
  calc
    m * ‖v‖ = Real.sqrt (m ^ 2 * inner ℝ v v) := by
      rw [real_inner_self_eq_norm_sq, Real.sqrt_mul (sq_nonneg m),
        Real.sqrt_sq hm0, Real.sqrt_sq (norm_nonneg v)]
    _ ≤ Real.sqrt ((intrinsicSpatialMetric g hrotation hcomplete).inner x v v) :=
      Real.sqrt_le_sqrt (intrinsicSpatialMetric_inner_lower
        g D hrotation hcomplete hsec hR hm0 hm hxR v)
    _ = _ := by
      rw [RiemannianMetric.tangentNorm, mfderiv_eq_fderiv]
      convert! congrArg Real.sqrt (intrinsicSpatialMetric_pullback
        g hrotation hcomplete x v v) using 1

end PoincareConjecture.M35.Uniqueness
