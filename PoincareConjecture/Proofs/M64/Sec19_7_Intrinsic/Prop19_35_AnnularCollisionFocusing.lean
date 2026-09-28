import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_WideCollisionFocusing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LongTwoSideRegion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_normal_collision_annular_focusing
    (N : IntrinsicAnnulus) {gamma₁ gamma₂ : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ gamma₁) (hb : ContDiff ℝ ∞ gamma₂)
    {a b A B r q h : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn gamma₁ (Icc 0 A)) (hbi : InjOn gamma₂ (Icc 0 B))
    (ha0 : gamma₁ 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : gamma₂ 0 = intrinsicAnnulusBoundary 1 b) (hmeet : gamma₁ A = gamma₂ B)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, gamma₁ s = gamma₂ t → s = A ∧ t = B)
    (horthA : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv gamma₁ 0) = 0)
    (horthB : N.metric.inner (intrinsicAnnulusBoundary 1 b)
      (deriv (intrinsicAnnulusBoundary 1) b) (deriv gamma₂ 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn gamma₁ (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn gamma₂ (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (gamma₁ t) (deriv gamma₁ t) (deriv gamma₁ t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (gamma₂ t) (deriv gamma₂ t) (deriv gamma₂ t) = 1)
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖gamma₁ t‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖gamma₂ t‖)
    (hinwardA : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (deriv gamma₁ 0))
    (hinwardB : 0 < inner ℝ (intrinsicAnnulusBoundary 1 b) (deriv gamma₂ 0))
    (hperiod : b - a < rampPeriod)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hAh : A ≤ h) (hBh : B ≤ h) (hhq : h ≤ q / 100)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (gamma₁ '' Icc 0 A ∪ gamma₂ '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    {curvatureCutoff : ℝ} (hcutoff : 100 * delta / q ≤ curvatureCutoff)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (height : ℝ → ℝ)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth0 : ∀ p, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward0 : ∀ p, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p, 0 < height p ∧
      (height p = h ∨ ‖e !₂[p, height p]‖ = 1 ∨ ‖e !₂[p, height p]‖ = 2))
    (hgeodesic : ∀ p, N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ curvatureCutoff →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) :
    intrinsicBoundaryLength N.metric 1 a b ≤ 2 * q ∧
    Real.cos (Real.sqrt (max K 1) * (q / 10)) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * (q / 10)) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  have hshort : intrinsicBoundaryLength N.metric 1 a b ≤ 2 * q := by
    by_contra hlong
    exact m64Intrinsic_no_long_two_side_region N hK hdelta hdeltaSmall hq hqr
      (hA.trans_le hAh) hhq hturn hcutoff harea hbudget hmodel hareaLoss
      hU hV hpV hbV hUV hcover hfV.symm hsub hab hperiod (lt_of_not_ge hlong)
      ha hb hA.le hB.le hAh hBh hai hbi ha0 hb0 haInterior hbInterior hunitA hunitB hfront
      e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric
  exact ⟨hshort, (m64Intrinsic_normal_collision_wide_focusing N ha hb hab hA hB hai hbi ha0 hb0
    hmeet hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior hinwardA hinwardB
    hperiod hshort hq hqr hAh hBh hhq hU hV hpV hbV hUV hcover hfV hfront hsub
    hK hdelta hdeltaSmall hturn harea hbudget hmodel).2.2⟩

end PoincareConjecture
