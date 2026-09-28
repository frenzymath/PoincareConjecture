import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalCollisionFocusing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalArcRetainedProducer
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalNormalCalculus





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_exists_regional_retained_endpoints
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
    (hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U)
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
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) :
    ∃ Z : Set ℝ, MeasurableSet Z ∧
      (∀ p ∈ Z, p ∈ Ioo l u ∧
        intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha ∧
        0 < height p ∧ height p < h) ∧
      InjOn (fun p => e !₂[p, height p]) Z ∧
      (∀ p ∈ Z, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[p, height p])) ∧
      (∀ p ∈ Z, e !₂[p, height p] ∈ frontier U) ∧
      87 * q / 100 < ∫ p in Z, intrinsicBoundarySpeed N.metric 1 p := by
  classical
  have hc : 0 < 1 - delta := by linarith
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  have hangle : Real.sqrt (max K 1) * (q / 10) ≤ Real.pi / 4 := by
    nlinarith only [hmodel, Real.pi_gt_three]
  have hrhoSmall : q / 10 ≤ q / (400 * delta) := by
    apply (le_div_iff₀ (by positivity : 0 < 400 * delta)).mpr
    nlinarith only [mul_lt_mul_of_pos_left hdeltaSmall hq, hq]
  have hturnQ : N.SmallBoundaryTurning delta q :=
    fun p w hpw hpwPeriod hpwLength => hturn p w hpw hpwPeriod (hpwLength.trans hqr)
  have hperiodJ : u ≤ l + rampPeriod := by linarith only [hperiod, hal, hub]
  have hsmooth (p : ℝ) : ContDiff ℝ ∞ (fun t => e !₂[p, t]) := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id)
  have hunit (p : ℝ) (hp : p ∈ Ioo l u) (hpos : 0 < height p) :
      ∀ t ∈ Icc 0 (height p), N.metric.inner (e !₂[p, t])
        (deriv (fun s => e !₂[p, s]) t) (deriv (fun s => e !₂[p, s]) t) = 1 := by
    have hzero : N.metric.inner (e !₂[p, 0])
        (curveVelocity (n := 2) (fun t => e !₂[p, t]) 0)
        (curveVelocity (n := 2) (fun t => e !₂[p, t]) 0) = 1 := by
      rw [m64Intrinsic_curveVelocity_eq_deriv, (hderiv p hp).deriv, hbase p hp]
      exact hunit0 p hp
    have hu := m64Intrinsic_geodesic_velocity_unit N hpos (hgeo p hp) Subset.rfl hzero
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hu
  have hfocus : ∀ p ∈ Ioo l u,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ w ∈ Ioo l u,
        intrinsicGeodesicCurvature N.metric N.connection 1 w ≤ alpha → p < w →
        (∃ t ∈ Icc 0 (height p), ∃ s ∈ Icc 0 (height w), e !₂[p, t] = e !₂[w, s]) →
        Real.cos (Real.sqrt (max K 1) * (q / 10)) *
          intrinsicBoundaryLength N.metric 1 p w ≤
          (Real.sin (Real.sqrt (max K 1) * (q / 10)) / Real.sqrt (max K 1)) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p w := by
    rintro p hp hk w hw hkw hpw ⟨t, ht, s, hs, heq⟩
    have htpos : 0 < t := by
      by_contra hn
      have ht0 : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
      rw [ht0, hbase p hp] at heq
      by_cases hs0 : s = 0
      · rw [hs0, hbase w hw] at heq
        exact hpw.ne (m64Intrinsic_boundary_injOn_short_arc
          (show u - l < rampPeriod by linarith only [hperiod, hal, hub])
          (Ioo_subset_Icc_self hp) (Ioo_subset_Icc_self hw) heq)
      have hnrm := hinside w hw hkw s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
      rw [← heq, m64Intrinsic_inner_boundary_norm] at hnrm
      exact (lt_irrefl (1 : ℝ)) hnrm
    have hspos : 0 < s := by
      by_contra hn
      have hs0 : s = 0 := le_antisymm (le_of_not_gt hn) hs.1
      rw [hs0, hbase w hw] at heq
      have hnrm := hinside p hp hk t ⟨htpos, ht.2⟩
      rw [heq, m64Intrinsic_inner_boundary_norm] at hnrm
      exact (lt_irrefl (1 : ℝ)) hnrm
    have hshort := (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero
      hp.1.le hpw.le hw.2.le).1
    rw [hlength] at hshort
    apply m64Intrinsic_regional_normal_collision_focusing N (hsmooth p) (hsmooth w)
      hpw htpos hspos
      ((hray p hp).mono (Icc_subset_Icc_right ht.2))
      ((hray w hw).mono (Icc_subset_Icc_right hs.2)) (hbase p hp) (hbase w hw) heq
      (by rw [(hderiv p hp).deriv]; exact horth p hp)
      (by rw [(hderiv w hw).deriv]; exact horth w hw)
      (fun x hx => hgeo p hp x ⟨hx.1, hx.2.trans ht.2⟩)
      (fun x hx => hgeo w hw x ⟨hx.1, hx.2.trans hs.2⟩)
      (fun x hx => hunit p hp (htpos.trans_le ht.2) x ⟨hx.1, hx.2.trans ht.2⟩)
      (fun x hx => hunit w hw (hspos.trans_le hs.2) x ⟨hx.1, hx.2.trans hs.2⟩)
      (fun x hx => hinside p hp hk x ⟨hx.1, hx.2.trans ht.2⟩)
      (fun x hx => hinside w hw hkw x ⟨hx.1, hx.2.trans hs.2⟩)
      (by rw [(hderiv p hp).deriv]; exact hinward p hp)
      (by rw [(hderiv w hw).deriv]; exact hinward w hw)
      (by linarith only [hp.1, hw.2, hal, hub, hperiod])
      (hshort.trans (sub_le_self _ (m64Intrinsic_boundaryLength_nonneg N 1 l p hp.1.le)))
      hq hqr (ht.2.trans (hcap p hp)) (hs.2.trans (hcap w hw)) hhq
      hU hV hpV hbV hUV hcover hfront hsub
    · exact (image_mono (Icc_subset_Icc (hal.trans hp.1.le) (hw.2.le.trans hub))).trans
        hcircle
    · intro x hx
      exact hconf p hp x ⟨hx.1, hx.2.trans ht.2⟩
    · intro x hx
      exact hconf w hw x ⟨hx.1, hx.2.trans hs.2⟩
    · exact hK
    · exact hdelta
    · exact hdeltaSmall
    · exact hturn
    · exact harea
    · exact hbudget
    · exact hmodel
  obtain ⟨E, _, _, _, _, hZ0, _, hEndpoint, _, _, hmass0⟩ :=
    m64Intrinsic_exists_local_arc_retained_strip N e (he.differentiable (by simp)) hheight
      hlu hperiodJ hlength hdelta hdeltaSmall hq hturnQ halpha
      hh (by positivity : 0 < q / 10) hkappa hangle hrhoSmall hareaLoss
      (fun p hp _ => hnonneg p hp) (fun p hp _ => hray p hp) hfocus
      (by
        intro x hx hk ht v
        have hxeta : !₂[x 0, x 1] = x := by ext i; fin_cases i <;> rfl
        have hm := hmetric (x 0) hx hk (x 1) ht v
        erw [hxeta] at hm
        simpa only [mfderiv_eq_fderiv] using! hm)
      (by
        intro x hx _ ht
        have hxeta : !₂[x 0, x 1] = x := by ext i; fin_cases i <;> rfl
        simpa only [hxeta] using hsub (hconf (x 0) hx (x 1) ht))
  let S := (Ioo l u ∩
    {p | intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha}) \ E
  let Z0 := S ∩ {p | height p < h}
  change MeasurableSet Z0 at hZ0
  change InjOn (fun p => e !₂[p, height p]) Z0 at hEndpoint
  change 87 * q / 100 < ∫ p in Z0, intrinsicBoundarySpeed N.metric 1 p at hmass0
  let Z := Z0 ∩ Good
  have hZ : MeasurableSet Z := hZ0.inter hGood
  have hZAE : Z =ᵐ[volume] Z0 := inter_ae_eq_left_of_ae_eq_univ hGoodAE
  have hmass : 87 * q / 100 < ∫ p in Z, intrinsicBoundarySpeed N.metric 1 p := by
    rw [setIntegral_congr_set hZAE]
    exact hmass0
  have hZdata (p : ℝ) (hp : p ∈ Z) : p ∈ Ioo l u ∧
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha ∧
      0 < height p ∧ height p < h :=
    ⟨hp.1.1.1.1, hp.1.1.1.2, hpositive p hp.1.1.1.1 hp.2, hp.1.2⟩
  refine ⟨Z, hZ, hZdata, hEndpoint.mono inter_subset_left, ?_, ?_, hmass⟩
  · intro p hp
    have hd := hZdata p hp
    have hi := m64Intrinsic_normal_map_injective_of_metric_lower N hc
      (x := !₂[p, height p]) (by
        simpa only [Matrix.cons_val_zero] using
          hmetric p hd.1 hd.2.1 (height p) ⟨hd.2.2.1.le, le_rfl⟩)
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
  · intro p hp
    have hd := hZdata p hp
    exact hcontact p hd.1 hd.2.2.1 hd.2.2.2

end PoincareConjecture
