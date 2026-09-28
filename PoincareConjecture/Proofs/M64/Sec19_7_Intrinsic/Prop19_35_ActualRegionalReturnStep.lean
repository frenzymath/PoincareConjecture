import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalEmbeddedContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalNormalCalculus
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalArcRetainedProducer
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseCentralReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralReturnChild
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedTransverseReturnLength













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_exists_actual_regional_return_step
    (N : IntrinsicAnnulus)
    {K delta r mu alpha R kappa : ℝ}
    (hK : N.GaussianCurvatureBound K)
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hr : 0 < r)
    (hturn : N.SmallBoundaryTurning delta r)
    (halpha : 100 * delta / r ≤ alpha)
    (hR : 0 < R) (hRshort : R < r / 20)
    (hkappa : 0 < kappa) (hangle : kappa * R ≤ Real.pi / 4)
    (hRfocus : R ≤ r / (400 * delta))
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric <
      (1 - delta) ^ 2 * R * (r / 10))
    {U V : Set AnnulusCoordinates}
    (hU : IsOpen U) (hV : IsOpen V) (hpV : IsPreconnected V)
    (hbV : ¬ Bornology.IsBounded V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b T : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hlong : r < intrinsicBoundaryLength N.metric 1 a b)
    {beta : ℝ → AnnulusCoordinates} (hbeta : ContDiff ℝ ∞ beta)
    (hT : 0 < T) (hTR : T < R) (hbetaInj : InjOn beta (Icc 0 T))
    (hends :
      (beta 0 = intrinsicAnnulusBoundary 1 a ∧
        beta T = intrinsicAnnulusBoundary 1 b) ∨
      (beta 0 = intrinsicAnnulusBoundary 1 b ∧
        beta T = intrinsicAnnulusBoundary 1 a))
    (hbetaInside : ∀ t ∈ Ioo 0 T, 1 < ‖beta t‖)
    (hbetaGeo : N.metric.IsGeodesicOn beta (Icc 0 T))
    (hbetaUnit0 : N.metric.inner (beta 0) (deriv beta 0) (deriv beta 0) = 1)
    (hfU : frontier U =
      intrinsicAnnulusBoundary 1 '' Icc a b ∪ beta '' Icc 0 T)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (annularHeight : ℝ → ℝ)
    (hbase : ∀ p ∈ Ioo a b, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p ∈ Ioo a b, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p ∈ Ioo a b,
      N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth : ∀ p ∈ Ioo a b, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward : ∀ p ∈ Ioo a b,
      0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p ∈ Ioo a b, 0 < annularHeight p ∧
      (annularHeight p = R ∨ ‖e !₂[p, annularHeight p]‖ = 1 ∨
        ‖e !₂[p, annularHeight p]‖ = 2))
    (hgeo : ∀ p ∈ Ioo a b, N.metric.IsGeodesicOn
      (fun t => e !₂[p, t]) (Icc 0 (annularHeight p)))
    (hmetric : ∀ p ∈ Ioo a b,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (annularHeight p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v))
    (hfocus : ∀ p ∈ Ioo a b,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ q ∈ Ioo a b,
        intrinsicGeodesicCurvature N.metric N.connection 1 q ≤ alpha → p < q →
        intrinsicBoundaryLength N.metric 1 p q ≤ r →
        ∀ Tp Tq : ℝ, 0 < Tp → Tp ≤ annularHeight p → Tp ≤ R →
          0 < Tq → Tq ≤ annularHeight q → Tq ≤ R →
          (∀ t ∈ Ioo 0 Tp, e !₂[p, t] ∈ U) →
          (∀ t ∈ Ioo 0 Tq, e !₂[q, t] ∈ U) →
          e !₂[p, Tp] = e !₂[q, Tq] →
          Real.cos (kappa * R) * intrinsicBoundaryLength N.metric 1 p q ≤
            (Real.sin (kappa * R) / kappa) *
              intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p q) :
    ∃ z ∈ Ioo a b, ∃ w ∈ Icc a b, ∃ T' : ℝ,
      0 < T' ∧ T' < R ∧ T' ≤ annularHeight z ∧
      intrinsicGeodesicCurvature N.metric N.connection 1 z ≤ alpha ∧
      let gamma : ℝ → AnnulusCoordinates := fun t => e !₂[z, t]
      ContDiff ℝ ∞ gamma ∧ InjOn gamma (Icc 0 T') ∧
      gamma 0 = intrinsicAnnulusBoundary 1 z ∧
      gamma T' = intrinsicAnnulusBoundary 1 w ∧
      HasDerivAt gamma (normal z) 0 ∧
      N.metric.IsGeodesicOn gamma (Icc 0 T') ∧
      (∀ t ∈ Icc 0 T', N.metric.inner (gamma t) (deriv gamma t) (deriv gamma t) = 1) ∧
      N.metric.inner (intrinsicAnnulusBoundary 1 z)
        (deriv (intrinsicAnnulusBoundary 1) z) (deriv gamma 0) = 0 ∧
      0 < inner ℝ (intrinsicAnnulusBoundary 1 z) (deriv gamma 0) ∧
      LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) w, deriv gamma T'] :
          Fin 2 → AnnulusCoordinates) ∧
      (∀ t ∈ Ioo 0 T', gamma t ∈ U) ∧
      (∀ t ∈ Ioo 0 T', 1 < ‖gamma t‖) ∧
      ∃ U' V' : Set AnnulusCoordinates,
        IsOpen U' ∧ IsOpen V' ∧ IsPathConnected U' ∧ IsPathConnected V' ∧
        Bornology.IsBounded U' ∧ ¬ Bornology.IsBounded V' ∧ Disjoint U' V' ∧
        U' ∪ V' =
          (intrinsicAnnulusBoundary 1 '' Icc (min z w) (max z w) ∪ gamma '' Icc 0 T')ᶜ ∧
        frontier U' =
          intrinsicAnnulusBoundary 1 '' Icc (min z w) (max z w) ∪ gamma '' Icc 0 T' ∧
        frontier V' =
          intrinsicAnnulusBoundary 1 '' Icc (min z w) (max z w) ∪ gamma '' Icc 0 T' ∧
        IsCompact (closure U') ∧ U' ⊆ U ∧ closure U' ⊆ closure U ∧
        closure U' ⊆ standardAnnulusDomain ∧
        r < intrinsicBoundaryLength N.metric 1 (min z w) (max z w) ∧
        intrinsicBoundaryLength N.metric 1 (min z w) (max z w) ≤
          intrinsicBoundaryLength N.metric 1 a b - r / 10 := by
  classical
  have hcmetric : 0 < 1 - delta := by linarith
  have hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi := by
    have hscaled := mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
    linarith [Real.pi_pos]
  have hcircleInj := m64Intrinsic_boundary_injOn_short_arc hperiod
  have hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U := by
    rw [hfU]
    exact subset_union_left
  have havoid : ∀ p ∈ Ioo a b, intrinsicAnnulusBoundary 1 p ∉ beta '' Icc 0 T := by
    rintro p hp ⟨t, ht, hpoint⟩
    have hpa : intrinsicAnnulusBoundary 1 p ≠ intrinsicAnnulusBoundary 1 a := by
      intro heq
      have h := hcircleInj (Ioo_subset_Icc_self hp) ⟨le_rfl, hab.le⟩ heq
      exact hp.1.ne' h
    have hpb : intrinsicAnnulusBoundary 1 p ≠ intrinsicAnnulusBoundary 1 b := by
      intro heq
      have h := hcircleInj (Ioo_subset_Icc_self hp) ⟨hab.le, le_rfl⟩ heq
      exact hp.2.ne h
    by_cases ht0 : t = 0
    · subst t
      rcases hends with h | h
      · exact hpa (hpoint.symm.trans h.1)
      · exact hpb (hpoint.symm.trans h.1)
    by_cases htT : t = T
    · subst t
      rcases hends with h | h
      · exact hpb (hpoint.symm.trans h.2)
      · exact hpa (hpoint.symm.trans h.2)
    have hnorm := hbetaInside t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htT⟩
    rw [hpoint, m64Intrinsic_inner_boundary_norm] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  obtain ⟨h, hh, _, hcontact, hray⟩ :=
    m64Intrinsic_exists_embedded_regional_contact_times N hK hsmall hcircleInj
      (isCompact_Icc.image hbeta.continuous) havoid hU hV hpV hbV hdisj hcover
      hfU hfront.symm hsub e he normal hbase hderiv hinward hunit0 hR annularHeight hAnn hgeo
  let ray : ℝ → ℝ → AnnulusCoordinates := fun p t => e !₂[p, t]
  have hraySmooth (p : ℝ) : ContDiff ℝ ∞ (ray p) := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun _ : ℝ => p)
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun t : ℝ => t)
      exact contDiff_id)
  have hrayInitial (p : ℝ) (hp : p ∈ Ioo a b) :
      N.metric.inner (ray p 0) (deriv (ray p) 0) (deriv (ray p) 0) = 1 := by
    rw [show deriv (ray p) 0 = normal p from (hderiv p hp).deriv]
    change N.metric.inner (e !₂[p, 0]) (normal p) (normal p) = 1
    erw [hbase p hp]
    exact hunit0 p hp
  have hrayOrth (p : ℝ) (hp : p ∈ Ioo a b) :
      N.metric.inner (intrinsicAnnulusBoundary 1 p)
        (deriv (intrinsicAnnulusBoundary 1) p) (deriv (ray p) 0) = 0 := by
    rw [show deriv (ray p) 0 = normal p from (hderiv p hp).deriv]
    exact horth p hp
  have hrayInward (p : ℝ) (hp : p ∈ Ioo a b) :
      0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (deriv (ray p) 0) := by
    rw [show deriv (ray p) 0 = normal p from (hderiv p hp).deriv]
    exact hinward p hp
  have hregular (p : ℝ) (hp : p ∈ Ioo a b)
      (hk : intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha)
      (t : ℝ) (ht : t ∈ Icc 0 (annularHeight p)) :
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[p, t]) := by
    have hi := m64Intrinsic_normal_map_injective_of_metric_lower N hcmetric
      (x := !₂[p, t]) (by simpa only [Matrix.cons_val_zero] using hmetric p hp hk t ht)
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
  obtain ⟨Good, hGood, _, hGoodAE, _, _, htransverse⟩ :=
    m64Intrinsic_exists_transverse_retained_bases e he
      (m64Intrinsic_contDiff_boundary 1) MeasurableSet.univ
  let H : ℝ → ℝ := Good.piecewise h 0
  have hHm : Measurable H := hh.piecewise hGood measurable_const
  have hHeq (p : ℝ) (hp : p ∈ Good) : H p = h p := piecewise_eq_of_mem Good h 0 hp
  have hHzero (p : ℝ) (hp : p ∉ Good) : H p = 0 := piecewise_eq_of_notMem Good h 0 hp
  have hHnonneg (p : ℝ) (hp : p ∈ Ioo a b) : 0 ≤ H p := by
    by_cases hg : p ∈ Good
    · rw [hHeq p hg]
      exact (hcontact p hp).1.le
    · rw [hHzero p hg]
  have hHle (p : ℝ) (hp : p ∈ Ioo a b) : H p ≤ h p := by
    by_cases hg : p ∈ Good
    · rw [hHeq p hg]
    · rw [hHzero p hg]
      exact (hcontact p hp).1.le
  have hHann (p : ℝ) (hp : p ∈ Ioo a b) : H p ≤ annularHeight p :=
    (hHle p hp).trans (hcontact p hp).2.2.1
  have hHcap (p : ℝ) (hp : p ∈ Ioo a b) : H p ≤ R :=
    (hHle p hp).trans (hcontact p hp).2.1
  have hHgood (p t : ℝ) (ht : 0 < t) (htH : t ≤ H p) : p ∈ Good := by
    by_contra hp
    rw [hHzero p hp] at htH
    exact (not_lt_of_ge htH) ht
  have hprefix (p : ℝ) (hp : p ∈ Ioo a b) {s : ℝ} (hs : s ≤ H p) :
      ∀ t ∈ Ioo 0 s, ray p t ∈ U := by
    intro t ht
    exact (hcontact p hp).2.2.2.1 t ⟨ht.1, ht.2.trans_le (hs.trans (hHle p hp))⟩
  have hHimage (p : ℝ) (hp : p ∈ Ioo a b) (t : ℝ) (ht : t ∈ Icc 0 (H p)) :
      e !₂[p, t] ∈ standardAnnulusDomain := by
    apply hsub
    by_cases ht0 : t = 0
    · rw [ht0, hbase p hp]
      exact frontier_subset_closure (hcircle (mem_image_of_mem _ (Ioo_subset_Icc_self hp)))
    by_cases hth : t = h p
    · rw [hth]
      exact (hcontact p hp).2.2.2.2.1
    · exact subset_closure ((hcontact p hp).2.2.2.1 t
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
          lt_of_le_of_ne (ht.2.trans (hHle p hp)) hth⟩)
  obtain ⟨c, hc, hlength⟩ := m64Intrinsic_exists_boundary_prefix_length N one_ne_zero hab hr hlong
  have hlocalParent : Ioo a c ⊆ Ioo a b := fun _ hp => ⟨hp.1, hp.2.trans hc.2⟩
  have hpairLength (p : ℝ) (hp : p ∈ Ioo a c) (q : ℝ) (hq : q ∈ Ioo a c) :
      intrinsicBoundaryLength N.metric 1 (min p q) (max p q) ≤ r := by
    have hlo : a ≤ min p q := le_min hp.1.le hq.1.le
    have hquant := (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero
      (a := a) (b := c) (c := min p q) (d := max p q)
      hlo min_le_max (max_le hp.2.le hq.2.le)).1
    rw [hlength] at hquant
    exact hquant.trans (sub_le_self _ (m64Intrinsic_boundaryLength_nonneg N 1 a _ hlo))

  have hnoReturn (p : ℝ) (hp : p ∈ Ioo a c)
      (hk : intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha)
      (hpGood : p ∈ Good) (q : ℝ) (hq : q ∈ Ioo a c)
      (s : ℝ) (hs : 0 < s) (hsH : s ≤ H p)
      (hpoint : ray p s = intrinsicAnnulusBoundary 1 q) : False := by
    have hpP := hlocalParent hp
    have hsAnn : s ≤ annularHeight p := hsH.trans (hHann p hpP)
    have hterminal : LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) q, deriv (ray p) s] :
          Fin 2 → AnnulusCoordinates) := by
      rw [m64Intrinsic_coordinate_normal_ray_deriv (he.differentiable (by simp) !₂[p, s])]
      exact htransverse p hpGood s q hpoint (hregular p hpP hk s ⟨hs.le, hsAnn⟩)
    have hlower := m64Intrinsic_nested_transverse_return_length_gt N hU hV hpV hbV
      hdisj hcover hfront hsub hcircle (Ioo_subset_Icc_self hpP)
      (Ioo_subset_Icc_self (hlocalParent hq)) hperiod hs (hraySmooth p)
      ((hray p hpP).mono (Icc_subset_Icc le_rfl (hsH.trans (hHle p hpP))))
      (hbase p hpP) hpoint (hprefix p hpP hsH)
      (fun t ht => hgeo p hpP t ⟨ht.1, ht.2.trans hsAnn⟩)
      (hrayInitial p hpP) (hrayOrth p hpP) (hrayInward p hpP) hterminal
      hK hturn harea hbudget
    exact (not_lt_of_ge (hpairLength p hp q hq)) hlower
  have hclosedFocus : ∀ p ∈ Ioo a c,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ q ∈ Ioo a c,
        intrinsicGeodesicCurvature N.metric N.connection 1 q ≤ alpha → p < q →
        (∃ t ∈ Icc 0 (H p), ∃ s ∈ Icc 0 (H q), e !₂[p, t] = e !₂[q, s]) →
        Real.cos (kappa * R) * intrinsicBoundaryLength N.metric 1 p q ≤
          (Real.sin (kappa * R) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p q := by
    rintro p hp hk q hq hkq hpq ⟨t, ht, s, hs, heq⟩
    have hpP := hlocalParent hp
    have hqP := hlocalParent hq
    by_cases ht0 : t = 0
    · subst t
      by_cases hs0 : s = 0
      · subst s
        rw [hbase p hpP, hbase q hqP] at heq
        exact False.elim (hpq.ne (hcircleInj (Ioo_subset_Icc_self hpP)
          (Ioo_subset_Icc_self hqP) heq))
      · have hspos := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        exact False.elim (hnoReturn q hq hkq (hHgood q s hspos hs.2) p hp s hspos hs.2
          (heq.symm.trans (hbase p hpP)))
    have htpos := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    by_cases hs0 : s = 0
    · subst s
      exact False.elim (hnoReturn p hp hk (hHgood p t htpos ht.2) q hq t htpos ht.2
        (heq.trans (hbase q hqP)))
    have hspos := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    apply hfocus p hpP hk q hqP hkq hpq
      (by simpa only [min_eq_left hpq.le, max_eq_right hpq.le] using hpairLength p hp q hq)
      t s htpos (ht.2.trans (hHann p hpP)) (ht.2.trans (hHcap p hpP))
      hspos (hs.2.trans (hHann q hqP)) (hs.2.trans (hHcap q hqP))
      (hprefix p hpP ht.2) (hprefix q hqP hs.2) heq
  obtain ⟨E, _, _, _, hS, hZ0, _, hEndpoint0, _, _, hmass0⟩ :=
    m64Intrinsic_exists_local_arc_retained_strip N e (he.differentiable (by simp)) hHm
      hc.1 (by linarith [hc.2]) hlength hdelta hdeltaSmall hr hturn halpha
      hR hR hkappa hangle hRfocus hareaLoss
      (fun p hp _ => hHnonneg p (hlocalParent hp))
      (fun p hp _ => (hray p (hlocalParent hp)).mono
        (Icc_subset_Icc le_rfl (hHle p (hlocalParent hp)))) hclosedFocus
      (by
        intro x hx hk ht v
        have hxeta : !₂[x 0, x 1] = x := by ext i; fin_cases i <;> rfl
        have h := hmetric (x 0) (hlocalParent hx) hk (x 1)
          ⟨ht.1, ht.2.trans (hHann (x 0) (hlocalParent hx))⟩ v
        erw [hxeta] at h
        simpa only [mfderiv_eq_fderiv] using! h)
      (by
        intro x hx _ ht
        have hxeta : !₂[x 0, x 1] = x := by ext i; fin_cases i <;> rfl
        simpa only [hxeta] using hHimage (x 0) (hlocalParent hx) (x 1) ht)
  let S := (Ioo a c ∩
    {p | intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha}) \ E
  let Z0 := S ∩ {p | H p < R}
  change MeasurableSet Z0 at hZ0
  change InjOn (fun p => e !₂[p, H p]) Z0 at hEndpoint0
  change 87 * r / 100 < ∫ p in Z0, intrinsicBoundarySpeed N.metric 1 p at hmass0
  let Z := Z0 ∩ Good
  have hZ : MeasurableSet Z := hZ0.inter hGood
  have hZAE : Z =ᵐ[volume] Z0 := inter_ae_eq_left_of_ae_eq_univ hGoodAE
  have hmass : 87 * r / 100 < ∫ p in Z, intrinsicBoundarySpeed N.metric 1 p := by
    rw [setIntegral_congr_set hZAE]
    exact hmass0
  have hZdata (p : ℝ) (hp : p ∈ Z) : p ∈ Ioo a b ∧
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha ∧ h p < R ∧ p ∈ Good := by
    rcases hp with ⟨⟨⟨⟨hp, hk⟩, _⟩, ht⟩, hg⟩
    exact ⟨hlocalParent hp, hk, (hHeq p hg) ▸ ht, hg⟩
  have hZsub : Z ⊆ Icc a b := fun p hp => Ioo_subset_Icc_self (hZdata p hp).1
  have hEndpoint : InjOn (fun p => e !₂[p, h p]) Z := by
    intro p hp q hq heq
    apply hEndpoint0 hp.1 hq.1
    change e !₂[p, H p] = e !₂[q, H q]
    rw [hHeq p hp.2, hHeq q hq.2]
    exact heq
  have hEndpointClass (p : ℝ) (hp : p ∈ Z) : e !₂[p, h p] ∈
      intrinsicAnnulusBoundary 1 '' Icc a b ∪ beta '' Icc 0 T := by
    have hd := hZdata p hp
    have hfrontier := ((hcontact p hd.1).2.2.2.2.2).resolve_left hd.2.2.1.ne
    rwa [hfU] at hfrontier
  have hbetaUnit : ∀ t ∈ Icc 0 T,
      N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1 := by
    have h := m64Intrinsic_geodesic_velocity_unit N hT hbetaGeo Subset.rfl
      (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hbetaUnit0)
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using h
  have hselectionBudget : T < (1 - delta) *
      ((∫ p in Z, intrinsicBoundarySpeed N.metric 1 p) - 2 * (r / 10)) := by
    have hpositive : 0 < (∫ p in Z, intrinsicBoundarySpeed N.metric 1 p) - 2 * (r / 10) := by
      linarith
    have hscaled := mul_lt_mul_of_pos_right
      (show (99 : ℝ) / 100 < 1 - delta by linarith) hpositive
    nlinarith only [hmass, hscaled, hTR, hRshort, hr]
  obtain ⟨z, hz, w, hw, hzab, hpoint, _, hleft, hright, hterminal⟩ :=
    m64Intrinsic_exists_transverse_central_circle_return N e he hh hab
      (by positivity : 0 < r / 10) (by linarith) hZ hZsub hEndpoint
      (fun p hp => hregular p (hZdata p hp).1 (hZdata p hp).2.1 (h p)
        ⟨(hcontact p (hZdata p hp).1).1.le, (hcontact p (hZdata p hp).1).2.2.1⟩)
      hbeta hT.le hbetaInj hbetaUnit hEndpointClass hcmetric.le
      (fun p hp => hmetric p (hZdata p hp).1 (hZdata p hp).2.1 (h p)
        ⟨(hcontact p (hZdata p hp).1).1.le, (hcontact p (hZdata p hp).1).2.2.1⟩)
      hselectionBudget
  have hzdata := hZdata z hz
  have hzcontact := hcontact z hzab
  have hgammaGeo : N.metric.IsGeodesicOn (ray z) (Icc 0 (h z)) :=
    fun t ht => hgeo z hzab t ⟨ht.1, ht.2.trans hzcontact.2.2.1⟩
  have hgammaUnit : ∀ t ∈ Icc 0 (h z),
      N.metric.inner (ray z t) (deriv (ray z) t) (deriv (ray z) t) = 1 := by
    have h := m64Intrinsic_geodesic_velocity_unit N hzcontact.1 hgammaGeo Subset.rfl
      (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hrayInitial z hzab)
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using h
  have hgammaTerminal : LinearIndependent ℝ
      (![deriv (intrinsicAnnulusBoundary 1) w, deriv (ray z) (h z)] :
        Fin 2 → AnnulusCoordinates) := by
    rw [m64Intrinsic_coordinate_normal_ray_deriv (he.differentiable (by simp) !₂[z, h z])]
    exact hterminal
  have hgammaInside : ∀ t ∈ Ioo 0 (h z), 1 < ‖ray z t‖ := fun t ht =>
    (m64Intrinsic_open_region_strictly_inside_annulus hU hsub
      (ray z t) (hzcontact.2.2.2.1 t ht)).1
  have hlower := m64Intrinsic_nested_transverse_return_length_gt N hU hV hpV hbV
    hdisj hcover hfront hsub hcircle (Ioo_subset_Icc_self hzab) hw hperiod hzcontact.1
    (hraySmooth z) (hray z hzab) (hbase z hzab) hpoint hzcontact.2.2.2.1 hgammaGeo
    (hrayInitial z hzab) (hrayOrth z hzab) (hrayInward z hzab) hgammaTerminal
    hK hturn harea hbudget
  obtain ⟨U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk',
      hchild, hclosure, hannulus, hloss⟩ :=
    m64Intrinsic_exists_central_return_child N hU hV hpV hbV hdisj hcover hfront hsub
      hcircle hperiod (Ioo_subset_Icc_self hzab) hw hzcontact.1 (hraySmooth z).continuous
      (hray z hzab) (hbase z hzab) hpoint hzcontact.2.2.2.1 hleft hright
  exact ⟨z, hzab, w, hw, h z, hzcontact.1, hzdata.2.2.1, hzcontact.2.2.1, hzdata.2.1,
    hraySmooth z, hray z hzab, hbase z hzab, hpoint, hderiv z hzab, hgammaGeo, hgammaUnit,
    hrayOrth z hzab, hrayInward z hzab, hgammaTerminal, hzcontact.2.2.2.1, hgammaInside,
    U', V', hU', hV', hpU', hpV', hbU', hbV', hd', hc', hfU', hfV', hk', hchild, hclosure,
    hannulus, hlower, hloss⟩

end PoincareConjecture
