import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionBoundaryCompetitor
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InteriorGeodesic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ENNReal Manifold ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_short_collision_minimizer
    (N : IntrinsicAnnulus) {K : Set AnnulusCoordinates} (hK : IsCompact K)
    {a b A B p : ℝ} (hp : p ∈ Icc a b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (hsideA : MapsTo alpha (Icc 0 A) K) (hsideB : MapsTo beta (Icc 0 B) K)
    (hbase : MapsTo (intrinsicAnnulusBoundary 1) (Icc a b) K) :
    ∃ (gamma : ℝ → AnnulusCoordinates) (L : ℝ),
      0 ≤ L ∧ L ≤ intrinsicBoundaryLength N.metric 1 a b / 2 + max A B ∧
      ContinuousOn gamma (Icc 0 L) ∧ gamma 0 = alpha A ∧
      gamma L = intrinsicAnnulusBoundary 1 p ∧ MapsTo gamma (Icc 0 L) K ∧
      InjOn gamma (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        m64IntrinsicCurveVariation N.metric gamma s t = ENNReal.ofReal (t - s)) ∧
      N.metric.IsGeodesicOn gamma {u | u ∈ Ioo 0 L ∧ gamma u ∈ interior K} ∧
      (∀ u ∈ Ioo 0 L, gamma u ∈ interior K →
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ gamma u) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
        ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
          tau 0 = gamma s → tau 1 = gamma t → MapsTo tau (Icc 0 1) K →
          ENNReal.ofReal (t - s) ≤ m64IntrinsicCurveVariation N.metric tau 0 1) := by
  obtain ⟨tau, htc, ht0, ht1, htconf, htvar⟩ :=
    m64Intrinsic_exists_short_collision_competitor N hp hA hB ha hb hunitA hunitB
      ha0 hb0 hmeet hsideA hsideB hbase
  let sigma := fun t : ℝ => tau (1 + (0 - 1) * t)
  have hparam : MapsTo (fun t : ℝ => 1 + (0 - 1) * t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsc : ContinuousOn sigma (Icc 0 1) :=
    htc.comp (by fun_prop) hparam
  have hs0 : sigma 0 = alpha A := by simpa only [sigma, mul_zero, add_zero] using ht1
  have hs1 : sigma 1 = intrinsicAnnulusBoundary 1 p := by
    simpa only [sigma, mul_one, add_sub_cancel] using ht0
  have hsvar : m64IntrinsicCurveVariation N.metric sigma 0 1 =
      m64IntrinsicCurveVariation N.metric tau 0 1 := by
    simpa only [min_eq_right zero_le_one, max_eq_left zero_le_one] using
      m64Intrinsic_curveVariation_affine N.metric tau 1 0
  have hbudget : 0 ≤ intrinsicBoundaryLength N.metric 1 a b / 2 + max A B :=
    add_nonneg (div_nonneg (m64Intrinsic_boundaryLength_nonneg N 1 a b (hp.1.trans hp.2))
      (by norm_num)) (hA.trans (le_max_left A B))
  obtain ⟨gamma, L, hL, hLB, hrest⟩ :=
    m64Intrinsic_exists_region_minimizer_geodesic_interior N.metric hK hsc hs0 hs1
      (htconf.comp hparam) (hsvar.le.trans htvar)
  exact ⟨gamma, L, hL, by simpa only [max_eq_left hbudget] using hLB, hrest⟩

end PoincareConjecture
