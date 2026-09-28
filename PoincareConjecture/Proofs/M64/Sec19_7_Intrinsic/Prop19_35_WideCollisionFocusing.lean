import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DoubleCollisionFocusing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_normal_collision_wide_focusing
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B r q h : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
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
    (hperiod : b - a < rampPeriod) (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ 2 * q)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hAh : A ≤ h) (hBh : B ≤ h) (hhq : h ≤ q / 100)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2) :
    intrinsicBoundaryLength N.metric 1 a b < 101 * q / 5000 ∧
    intrinsicBoundaryLength N.metric 1 a b / 2 + max A B < 201 * q / 10000 ∧
    Real.cos (Real.sqrt (max K 1) * (q / 10)) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (Real.sqrt (max K 1) * (q / 10)) / Real.sqrt (max K 1)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  have hh : 0 < h := hA.trans_le hAh
  have hmax : max A B ≤ h := max_le hAh hBh
  have hR0 : 0 < q + h := by positivity
  have hR0bound : q + h ≤ 101 * q / 100 := by linarith only [hhq]
  have hangle0 : Real.sqrt (max K 1) * (q + h) ≤ Real.pi / 4 := by
    have hs := mul_le_mul_of_nonneg_left hhq hkappa.le
    nlinarith only [hs, hmodel, Real.pi_gt_three]
  have hradius0 : intrinsicBoundaryLength N.metric 1 a b / 2 + max A B ≤ q + h := by
    linarith only [hshort, hmax]
  have hfocus0 := (m64Intrinsic_normal_collision_focusing N ha hb hab hA hB hai hbi ha0 hb0
    hmeet hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior hinwardA hinwardB
    hperiod (hshort.trans hqr) hU hV hpV hbV hUV hcover hfV hfront hsub hK hdelta hturn
    harea hbudget hradius0 hangle0).2
  have hturnLocal := hturn a b hab.le (by linarith only [hperiod]) (hshort.trans hqr)
  have hlen : intrinsicBoundaryLength N.metric 1 a b < 101 * q / 5000 := by
    have ht := hfocus0.trans_lt (mul_lt_mul_of_pos_left hturnLocal
      (mul_pos (by norm_num : (0 : ℝ) < 2) hR0))
    have hd := mul_lt_mul_of_pos_left hdeltaSmall
      (mul_pos (by norm_num : (0 : ℝ) < 2) hR0)
    nlinarith only [ht, hd, hR0bound]
  have hradius : intrinsicBoundaryLength N.metric 1 a b / 2 + max A B < 201 * q / 10000 := by
    linarith only [hlen, hmax, hhq]
  have hradius' : intrinsicBoundaryLength N.metric 1 a b / 2 + max A B ≤ q / 10 := by
    linarith only [hradius, hq]
  have hangle : Real.sqrt (max K 1) * (q / 10) ≤ Real.pi / 4 := by
    nlinarith only [hmodel, Real.pi_gt_three]
  exact ⟨hlen, hradius, (m64Intrinsic_normal_collision_focusing N ha hb hab hA hB hai hbi
    ha0 hb0 hmeet hsides horthA horthB hgeoA hgeoB hunitA hunitB haInterior hbInterior
    hinwardA hinwardB hperiod (hshort.trans hqr) hU hV hpV hbV hUV hcover hfV hfront hsub
    hK hdelta hturn harea hbudget hradius' hangle).1⟩

end PoincareConjecture
