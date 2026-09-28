import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionMinimizer









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_exists_short_base_to_vertex_minimizer
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
      ContinuousOn gamma (Icc 0 L) ∧ gamma 0 = intrinsicAnnulusBoundary 1 p ∧
      gamma L = alpha A ∧ MapsTo gamma (Icc 0 L) K ∧ InjOn gamma (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        N.metric.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|) ∧
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
  obtain ⟨gamma, L, hL, hLB, hc, hg0, hgL, hconf, hinj, hlip, hvar, hmin⟩ :=
    m64Intrinsic_exists_embedded_region_minimizer N.metric hK htc ht0 ht1 htconf htvar
  have hbudget : 0 ≤ intrinsicBoundaryLength N.metric 1 a b / 2 + max A B :=
    add_nonneg (div_nonneg (m64Intrinsic_boundaryLength_nonneg N 1 a b (hp.1.trans hp.2))
      (by norm_num)) (hA.trans (le_max_left A B))
  obtain ⟨hgeo, hsmooth⟩ :=
    m64Intrinsic_constrained_minimizer_interior_geodesic N.metric hK hlip hmin
  exact ⟨gamma, L, hL, by simpa only [max_eq_left hbudget] using hLB,
    hc, hg0, hgL, hconf, hinj, hlip, hvar, hgeo, hsmooth, hmin⟩

end PoincareConjecture
