import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedCollisionRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DoubleCollisionFocusing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_regional_normal_collision_focusing
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B r q h : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (horthA : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv alpha 0) = 0)
    (horthB : N.metric.inner (intrinsicAnnulusBoundary 1 b)
      (deriv (intrinsicAnnulusBoundary 1) b) (deriv beta 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖alpha t‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hinwardA : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (deriv alpha 0))
    (hinwardB : 0 < inner ℝ (intrinsicAnnulusBoundary 1 b) (deriv beta 0))
    (hperiod : b - a < rampPeriod) (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ q)
    (hq : 0 < q) (hqr : q ≤ r) (hAh : A ≤ h) (hBh : B ≤ h) (hhq : h ≤ q / 100)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    (hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U)
    (hconfA : MapsTo alpha (Icc 0 A) (closure U))
    (hconfB : MapsTo beta (Icc 0 B) (closure U))
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2) :
    Real.cos (Real.sqrt (max K 1) * (q / 10)) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * (q / 10)) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  obtain ⟨s, t, hs, hsA, ht, htB, hst, hfirst, W, Y, hW, hY, _, hpY, _, hbY,
      hWY, hcW, hfY, hfW, _, _, _, hWsub⟩ :=
    m64Intrinsic_exists_nested_collision_region hU hV hpV hbV hUV hcover hfront hsub
      hab hperiod hA hB ha.continuous hb.continuous hai hbi ha0 hb0 haInterior hbInterior
      hcircle hconfA hconfB hmeet
  exact (m64Intrinsic_normal_collision_double_focusing N ha hb hab hs ht
    (hai.mono (Icc_subset_Icc_right hsA)) (hbi.mono (Icc_subset_Icc_right htB))
    ha0 hb0 hst hfirst horthA horthB
    (fun x hx => hgeoA x ⟨hx.1, hx.2.trans hsA⟩)
    (fun y hy => hgeoB y ⟨hy.1, hy.2.trans htB⟩)
    (fun x hx => hunitA x ⟨hx.1, hx.2.trans hsA⟩)
    (fun y hy => hunitB y ⟨hy.1, hy.2.trans htB⟩)
    (fun x hx => haInterior x ⟨hx.1, hx.2.trans hsA⟩)
    (fun y hy => hbInterior y ⟨hy.1, hy.2.trans htB⟩)
    hinwardA hinwardB hperiod hshort hq hqr (hsA.trans hAh) (htB.trans hBh) hhq
    hW hY hpY.isConnected.isPreconnected hbY hWY hcW hfY hfW hWsub
    hK hdelta hdeltaSmall hturn harea hbudget hmodel).2.2

end PoincareConjecture
