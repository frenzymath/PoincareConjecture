import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCenterNormalization
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem radial_core_scalar_witness
    (P : M35StandardCapPredecessors) (g : RiemannianMetric 3 StandardCapSpace)
    (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {a : ℝ} (ha : 0 < a) (y : StandardCapSpace)
    (hfar : 2 * intrinsicWarpingRadius g hrotation hcomplete a ≤ radialArclength g ‖y‖)
    (hinner : radialArclength g ‖y‖ ≤ a) :
    1 ≤ intrinsicWarpingRadius g hrotation hcomplete a ^ 2 * D.scalarCurvature y := by
  let f := intrinsicWarpingRadius g hrotation hcomplete a
  have hf : 0 < f := intrinsicWarpingRadius_pos g hrotation hcomplete ha
  have hs : 0 < radialArclength g ‖y‖ := (mul_pos (by norm_num) hf).trans_le hfar
  have hy : y ≠ 0 := by
    intro hy
    simp only [hy, norm_zero, radialArclength_zero, lt_self_iff_false] at hs
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hsmall : axisWarpingRadius g ‖y‖ ≤ f := by
    rw [← intrinsicWarpingRadius_radialArclength g hrotation hcomplete]
    exact intrinsicWarpingRadius_monotoneOn g hrotation hcomplete D hsec hs ha hinner
  have hu := axisWarpingSlope_nonneg D hrotation hsec hcomplete hr
  have hmean := (axisWarpingSlope_mul_arclength_le D hrotation hsec hr).trans hsmall
  have hproduct := mul_le_mul_of_nonneg_left hfar hu
  have huhalf : axisWarpingSlope g ‖y‖ ≤ 1 / 2 := by
    have hh : (2 * axisWarpingSlope g ‖y‖) * f ≤ 1 * f := by
      nlinarith only [hmean, hproduct]
    have htwo := (mul_le_mul_iff_of_pos_right hf).mp hh
    linarith only [htwo]
  have husq : axisWarpingSlope g ‖y‖ ^ 2 ≤ 1 / 4 := by
    nlinarith only [hu, huhalf,
      mul_nonneg hu (sub_nonneg.mpr huhalf)]
  have hscalar := scalar_mul_axisWarpingRadius_sq_ge D hrotation hsec hr
  rw [← (rotational_scalar_edist_eq_axis P D hrotation y).1] at hscalar
  have hRpos : 0 < D.scalarCurvature y := by
    by_contra hbad
    have hprod := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hbad)
      (sq_nonneg (axisWarpingRadius g ‖y‖))
    nlinarith only [hscalar, husq, hprod]
  have hsq : axisWarpingRadius g ‖y‖ ^ 2 ≤ f ^ 2 :=
    pow_le_pow_left₀ (axisWarpingRadius_pos g hr).le hsmall 2
  have hmul := mul_le_mul_of_nonneg_left hsq hRpos.le
  change 1 ≤ f ^ 2 * D.scalarCurvature y
  nlinarith only [hscalar, husq, hmul]

end PoincareConjecture.M35.Uniqueness
