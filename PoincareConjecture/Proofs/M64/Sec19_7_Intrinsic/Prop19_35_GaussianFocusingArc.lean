import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingNorm
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingField
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingSegment

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_sine_focusing_base_length_lt_of_small_turning
    (N : IntrinsicAnnulus) {delta r R κ L a b : ℝ}
    (hturning : N.SmallBoundaryTurning delta r)
    (hab : a ≤ b) (hperiod : b ≤ a + rampPeriod)
    (hsub : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    (hR : 0 < R) (hκ : 0 < κ)
    (hκone : 1 ≤ κ)
    (hangle : κ * R ≤ Real.pi / 4)
    (hL : 0 ≤ L)
    (hendpoint : Real.cos (κ * R) * L ≤
      (Real.sin (κ * R) / κ) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) :
    L < delta := by
  have hendpoint' : Real.cos (κ * R) * L ≤
      Real.sin (κ * R) * (κ⁻¹ *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hendpoint
  have hturn : 0 ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b :=
    m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab
  have hturn_scaled : 0 ≤ κ⁻¹ *
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b :=
    mul_nonneg (inv_nonneg.mpr hκ.le) hturn
  have hbase := m64Intrinsic_scaled_focusing_base_length_le_turning
    (T := κ⁻¹ * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b)
    hR hκ hangle hL hturn_scaled hendpoint'
  have hsmall : intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b < delta := by
    simpa only [IntrinsicAnnulus.SmallBoundaryTurning] using
      hturning a b hab hperiod hsub
  have hscaled : κ⁻¹ *
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
    have h := mul_le_mul_of_nonneg_right
      (inv_le_one_of_one_le₀ hκone) hturn
    simpa only [one_mul] using h
  exact hbase.trans_lt (hscaled.trans_lt hsmall)

end PoincareConjecture
