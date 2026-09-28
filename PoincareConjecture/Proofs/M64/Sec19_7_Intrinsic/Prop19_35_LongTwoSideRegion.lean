import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoSideRegionalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalNormalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralBoundaryInterval
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedReturnRegion





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_no_long_two_side_region
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : 2 * q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hlong : 2 * q < intrinsicBoundaryLength N.metric 1 a b)
    {gamma₁ gamma₂ : ℝ → AnnulusCoordinates}
    (hgamma₁ : ContDiff ℝ ∞ gamma₁) (hgamma₂ : ContDiff ℝ ∞ gamma₂)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAh : A ≤ h) (hBh : B ≤ h)
    (hinj₁ : InjOn gamma₁ (Icc 0 A)) (hinj₂ : InjOn gamma₂ (Icc 0 B))
    (hstart₁ : gamma₁ 0 = intrinsicAnnulusBoundary 1 a)
    (hstart₂ : gamma₂ 0 = intrinsicAnnulusBoundary 1 b)
    (hinside₁ : ∀ t ∈ Ioc 0 A, 1 < ‖gamma₁ t‖)
    (hinside₂ : ∀ t ∈ Ioc 0 B, 1 < ‖gamma₂ t‖)
    (hunit₁ : ∀ t ∈ Icc 0 A,
      N.metric.inner (gamma₁ t) (deriv gamma₁ t) (deriv gamma₁ t) = 1)
    (hunit₂ : ∀ t ∈ Icc 0 B,
      N.metric.inner (gamma₂ t) (deriv gamma₂ t) (deriv gamma₂ t) = 1)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (gamma₁ '' Icc 0 A ∪ gamma₂ '' Icc 0 B))
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
    (hmetric : ∀ p, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) : False := by
  obtain ⟨l, u, hal, hlu, hub, hlength, _⟩ :=
    m64Intrinsic_exists_central_boundary_interval N hab hq hlong
  obtain ⟨p, hp, w, hw, s, hs, hsHeight, hsi, hprefix, hpoint, hterminal⟩ :=
    m64Intrinsic_exists_two_side_regional_return N hK hdelta hdeltaSmall hq
      (by linarith only [hqr, hq]) hh hhq hturn halpha harea hbudget hmodel hareaLoss
      hU hV hpV hbV hUV hcover hfront hsub hal.le hlu hub.le hperiod hlength
      hgamma₁ hgamma₂ hA hB hAh hBh hinj₁ hinj₂ hstart₁ hstart₂ hinside₁ hinside₂
      hunit₁ hunit₂ hfU e he normal height (fun p _ => hbase p) (fun p _ => hderiv p)
      (fun p _ => hunit0 p) (fun p _ => horth0 p) (fun p _ => hinward0 p)
      (fun p _ => hAnn p) (fun p _ => hgeodesic p) (fun p _ => hmetric p)
  have hpab : p ∈ Ioo a b := ⟨hal.trans hp.1, hp.2.trans hub⟩
  let ray : ℝ → AnnulusCoordinates := fun t => e !₂[p, t]
  have hray : ContDiff ℝ ∞ ray := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id)
  have h0 : ray 0 = intrinsicAnnulusBoundary 1 p := hbase p
  have hd0 : deriv ray 0 = normal p := (hderiv p).deriv
  have hpw : p ≠ w := by
    intro heq
    have hpoints : ray 0 = ray s := h0.trans ((congrArg _ heq).trans hpoint.symm)
    exact hs.1.ne (hsi ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hpoints)
  have hends :
      (ray 0 = intrinsicAnnulusBoundary 1 (min p w) ∧
        ray s = intrinsicAnnulusBoundary 1 (max p w)) ∨
      (ray 0 = intrinsicAnnulusBoundary 1 (max p w) ∧
        ray s = intrinsicAnnulusBoundary 1 (min p w)) := by
    rcases le_total p w with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact Or.inl ⟨h0, hpoint⟩
    · rw [min_eq_right h, max_eq_left h]
      exact Or.inr ⟨h0, hpoint⟩
  have hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U := by
    rw [hfU]
    exact subset_union_left
  obtain ⟨W, Y, hW, hY, _, hpY, _, hbY, hd, hc, hfW, hfY, _, _, _, hsubW⟩ :=
    m64Intrinsic_exists_nested_inner_return_region hU hV hpV hbV hUV hcover hfront hsub
      hcircle (le_min hpab.1.le hw.1) (min_lt_max.mpr hpw) (max_le hpab.2.le hw.2)
      hperiod hs.1 hray.continuous hsi hends hprefix
  apply m64Intrinsic_no_regional_normal_return N hK hdelta hdeltaSmall hq hqr hh hhq
    hturn halpha harea hbudget hmodel hareaLoss hray hs.1 hs.2 hsi h0 hpoint
    (fun t ht => (m64Intrinsic_open_region_strictly_inside_annulus hU hsub _
      (hprefix t ht)).1)
    (fun t ht => hgeodesic p t ⟨ht.1, ht.2.trans hsHeight⟩)
    (by rw [h0, hd0]; exact hunit0 p)
    (by rw [hd0]; exact horth0 p)
    (by rw [hd0]; exact hinward0 p) hterminal
    (by rw [abs_lt]; constructor <;> linarith only [hperiod, hpab.1, hpab.2, hw.1, hw.2])
    hW hY hpY.isConnected.isPreconnected hbY hd
    (by simpa only [hfW] using hc) (hfW.trans hfY.symm) hsubW hfW
    e he normal height hbase hderiv hunit0 horth0 hinward0 hAnn hgeodesic hmetric

end PoincareConjecture
