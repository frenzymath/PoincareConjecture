import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalRetainedEndpoints
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurveEndpointProjection





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_no_inner_contact_regional_capacity
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b l u : ℝ} (hal : a ≤ l) (hlu : l < u) (hub : u ≤ b)
    (hperiod : b - a < rampPeriod) (hlength : intrinsicBoundaryLength N.metric 1 l u = q)
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    {T : ℝ} (hT : 0 ≤ T) (hTh : T ≤ h) (htargetInj : InjOn target (Icc 0 T))
    (hunitTarget : ∀ t ∈ Icc 0 T,
      N.metric.inner (target t) (deriv target t) (deriv target t) = 1)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ target '' Icc 0 T)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) {height : ℝ → ℝ} (hheight : Measurable height)
    {Good : Set ℝ} (hGood : MeasurableSet Good) (hGoodAE : Good =ᵐ[volume] univ)
    (hpositive : ∀ p ∈ Ioo l u, p ∈ Good → 0 < height p)
    (hnonneg : ∀ p ∈ Ioo l u, 0 ≤ height p)
    (hcap : ∀ p ∈ Ioo l u, height p ≤ h)
    (hbase : ∀ p ∈ Ioo l u, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p ∈ Ioo l u, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p ∈ Ioo l u,
      N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth : ∀ p ∈ Ioo l u, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward : ∀ p ∈ Ioo l u, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hgeo : ∀ p ∈ Ioo l u,
      N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hray : ∀ p ∈ Ioo l u, InjOn (fun t => e !₂[p, t]) (Icc 0 (height p)))
    (hconf : ∀ p ∈ Ioo l u, ∀ t ∈ Icc 0 (height p), e !₂[p, t] ∈ closure U)
    (hinside : ∀ p ∈ Ioo l u,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Ioc 0 (height p), 1 < ‖e !₂[p, t]‖)
    (hcontact : ∀ p ∈ Ioo l u, 0 < height p → height p < h →
      e !₂[p, height p] ∈ frontier U)
    (hmetric : ∀ p ∈ Ioo l u,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (height p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) : False := by
  have hc : 0 < 1 - delta := by linarith only [hdeltaSmall]
  obtain ⟨Z, hZ, hZdata, hEndpoint, hregular, hfrontier, hmass⟩ :=
    m64Intrinsic_exists_regional_retained_endpoints N hK hdelta hdeltaSmall hq hqr hh hhq
      hturn halpha harea hbudget hmodel hareaLoss hU hV hpV hbV hUV hcover hfront hsub
      hal hlu hub hperiod hlength (by rw [hfU]; exact subset_union_left)
      e he normal hheight hGood hGoodAE hpositive hnonneg hcap hbase hderiv hunit0
      horth hinward hgeo hray hconf hinside hcontact hmetric
  have hcapacity := m64Intrinsic_unit_curve_endpoint_projection_length_le N e he hheight hZ
    (fun p hp => Ioo_subset_Icc_self (hZdata p hp).1) hEndpoint hregular
    htarget hT htargetInj hunitTarget
    (by
      intro p hp
      have hd := hZdata p hp
      have hf := hfrontier p hp
      rw [hfU] at hf
      rcases hf with ⟨w, _, heq⟩ | ht
      · have hn := hinside p hd.1 hd.2.1 (height p) ⟨hd.2.2.1, le_rfl⟩
        rw [← heq, m64Intrinsic_inner_boundary_norm] at hn
        exact ((lt_irrefl (1 : ℝ)) hn).elim
      · exact ht)
    hc.le (fun p hp => hmetric p (hZdata p hp).1 (hZdata p hp).2.1
      (height p) ⟨(hZdata p hp).2.2.1.le, le_rfl⟩)
  have hscaled := mul_lt_mul_of_pos_left hmass hc
  have hdeltaQ := mul_lt_mul_of_pos_right hdeltaSmall hq
  simp only [sub_zero] at hcapacity
  nlinarith only [hscaled, hcapacity, hTh, hhq, hdeltaQ, hq]

end PoincareConjecture
