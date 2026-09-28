import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalCentralReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralBoundaryInterval
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralReturnChild
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedTransverseReturnLength





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_no_central_regional_return
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
    {a b T : ℝ} (hab : a < b) (hperiod : b - a < rampPeriod)
    (hlong : r < intrinsicBoundaryLength N.metric 1 a b)
    {beta : ℝ → AnnulusCoordinates} (hbeta : ContDiff ℝ ∞ beta)
    (hT : 0 < T) (hTh : T ≤ h) (hbetaInj : InjOn beta (Icc 0 T))
    (hends : (beta 0 = intrinsicAnnulusBoundary 1 a ∧
        beta T = intrinsicAnnulusBoundary 1 b) ∨
      (beta 0 = intrinsicAnnulusBoundary 1 b ∧ beta T = intrinsicAnnulusBoundary 1 a))
    (hbetaInside : ∀ t ∈ Ioo 0 T, 1 < ‖beta t‖)
    (hbetaGeo : N.metric.IsGeodesicOn beta (Icc 0 T))
    (hbetaUnit0 : N.metric.inner (beta 0) (deriv beta 0) (deriv beta 0) = 1)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ beta '' Icc 0 T)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (annularHeight : ℝ → ℝ)
    (hbase : ∀ p ∈ Ioo a b, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p ∈ Ioo a b, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p ∈ Ioo a b,
      N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth : ∀ p ∈ Ioo a b, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward : ∀ p ∈ Ioo a b, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p ∈ Ioo a b, 0 < annularHeight p ∧
      (annularHeight p = h ∨ ‖e !₂[p, annularHeight p]‖ = 1 ∨
        ‖e !₂[p, annularHeight p]‖ = 2))
    (hgeo : ∀ p ∈ Ioo a b,
      N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (annularHeight p)))
    (hmetric : ∀ p ∈ Ioo a b,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (annularHeight p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) : False := by
  classical
  let P (c d Tc : ℝ) (gamma : ℝ → AnnulusCoordinates)
      (W Y : Set AnnulusCoordinates) : Prop :=
    r < intrinsicBoundaryLength N.metric 1 c d ∧
    a ≤ c ∧ c < d ∧ d ≤ b ∧ W ⊆ U ∧
    IsOpen W ∧ IsOpen Y ∧ IsPreconnected Y ∧
    ¬ Bornology.IsBounded Y ∧ Disjoint W Y ∧
    W ∪ Y = (frontier W)ᶜ ∧ frontier W = frontier Y ∧
    closure W ⊆ standardAnnulusDomain ∧
    ContDiff ℝ ∞ gamma ∧ 0 < Tc ∧ Tc ≤ h ∧ InjOn gamma (Icc 0 Tc) ∧
    ((gamma 0 = intrinsicAnnulusBoundary 1 c ∧ gamma Tc = intrinsicAnnulusBoundary 1 d) ∨
      (gamma 0 = intrinsicAnnulusBoundary 1 d ∧ gamma Tc = intrinsicAnnulusBoundary 1 c)) ∧
    (∀ t ∈ Ioo 0 Tc, 1 < ‖gamma t‖) ∧ N.metric.IsGeodesicOn gamma (Icc 0 Tc) ∧
    N.metric.inner (gamma 0) (deriv gamma 0) (deriv gamma 0) = 1 ∧
    frontier W = intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 Tc
  let D : Set ℝ := {L | ∃ (c d Tc : ℝ) (gamma : ℝ → AnnulusCoordinates)
    (W Y : Set AnnulusCoordinates), P c d Tc gamma W Y ∧
      L = intrinsicBoundaryLength N.metric 1 c d}
  have hDnonempty : D.Nonempty := by
    refine ⟨intrinsicBoundaryLength N.metric 1 a b, a, b, T, beta, U, V, ?_, rfl⟩
    exact ⟨hlong, le_rfl, hab, le_rfl, Subset.rfl, hU, hV, hpV, hbV,
      hUV, hcover, hfront, hsub, hbeta, hT, hTh, hbetaInj, hends,
      hbetaInside, hbetaGeo, hbetaUnit0, hfU⟩
  have hDbdd : BddBelow D := by
    refine ⟨r, ?_⟩
    rintro L ⟨c, d, Tc, gamma, W, Y, hP, rfl⟩
    exact hP.1.le
  have hdescend : ∀ L ∈ D, ∃ L' ∈ D, L' ≤ L - q / 10 := by
    rintro L ⟨c, d, Tc, gamma, W, Y, hP, hL⟩
    rcases hP with ⟨hlongC, hac, hcd, hdb, hWU, hW, hY, hpY, hbY, hd,
      hc, hf, hs, hg, hTc, hTch, hgi, hge, hinside, hgg, hgu, hfW⟩
    have hparameters : Ioo c d ⊆ Ioo a b :=
      fun _ hp => ⟨hac.trans_lt hp.1, hp.2.trans_le hdb⟩
    have hperiodC : d - c < rampPeriod := (sub_le_sub hdb hac).trans_lt hperiod
    have hcircle : intrinsicAnnulusBoundary 1 '' Icc c d ⊆ frontier W := by
      rw [hfW]
      exact subset_union_left
    obtain ⟨l, u, hcl, hlu, hud, hlength, hcentral⟩ :=
      m64Intrinsic_exists_central_boundary_interval N hcd hq (hqr.trans_lt hlongC)
    obtain ⟨p, hp, w, hw, s, hslen, hsAnn, hsi, hprefix, hpoint, hterminal⟩ :=
      m64Intrinsic_exists_regional_central_return N hK hdelta hdeltaSmall hq
        (by linarith only [hqr, hq]) hh hhq hturn halpha harea hbudget hmodel hareaLoss
        hW hY hpY hbY hd hc hf hs hcl.le hlu hud.le hperiodC hlength
        hg hTc hTch hgi hge hinside hgg hgu hfW e he normal annularHeight
        (fun p hp => hbase p (hparameters hp))
        (fun p hp => hderiv p (hparameters hp))
        (fun p hp => hunit0 p (hparameters hp))
        (fun p hp => horth p (hparameters hp))
        (fun p hp => hinward p (hparameters hp))
        (fun p hp => hAnn p (hparameters hp))
        (fun p hp => hgeo p (hparameters hp))
        (fun p hp => hmetric p (hparameters hp))
    have hpC : p ∈ Ioo c d := ⟨hcl.trans hp.1, hp.2.trans hud⟩
    have hpP := hparameters hpC
    let ray : ℝ → AnnulusCoordinates := fun t => e !₂[p, t]
    have hray : ContDiff ℝ ∞ ray := he.comp (by
      apply (contDiff_piLp 2).mpr
      intro i
      fin_cases i
      · exact contDiff_const
      · exact contDiff_id)
    have h0 : ray 0 = intrinsicAnnulusBoundary 1 p := hbase p hpP
    have hd0 : deriv ray 0 = normal p := (hderiv p hpP).deriv
    have hrayGeo : N.metric.IsGeodesicOn ray (Icc 0 s) :=
      fun t ht => hgeo p hpP t ⟨ht.1, ht.2.trans hsAnn⟩
    have hrayUnit0 : N.metric.inner (ray 0) (deriv ray 0) (deriv ray 0) = 1 := by
      rw [h0, hd0]
      exact hunit0 p hpP
    have hrayOrth : N.metric.inner (intrinsicAnnulusBoundary 1 p)
        (deriv (intrinsicAnnulusBoundary 1) p) (deriv ray 0) = 0 := by
      rw [hd0]
      exact horth p hpP
    have hrayInward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (deriv ray 0) := by
      rw [hd0]
      exact hinward p hpP
    have hlower := m64Intrinsic_nested_transverse_return_length_gt N hW hY hpY hbY
      hd hc hf hs hcircle (Ioo_subset_Icc_self hpC) hw hperiodC hslen.1 hray hsi h0
      hpoint hprefix hrayGeo hrayUnit0 hrayOrth hrayInward hterminal hK hturn harea hbudget
    obtain ⟨W', Y', hW', hY', _, hpY', _, hbY', hd', hc', hfW', hfY', _, hchild,
        _, hsub', hloss⟩ :=
      m64Intrinsic_exists_central_return_child N hW hY hpY hbY hd hc hf hs hcircle hperiodC
        (Ioo_subset_Icc_self hpC) hw hslen.1 hray.continuous hsi h0 hpoint hprefix
        (hcentral p (Ioo_subset_Icc_self hp)).1 (hcentral p (Ioo_subset_Icc_self hp)).2
    have hpw : p ≠ w := by
      intro heq
      have he := h0.trans ((congrArg (intrinsicAnnulusBoundary 1) heq).trans hpoint.symm)
      exact hslen.1.ne (hsi ⟨le_rfl, hslen.1.le⟩ ⟨hslen.1.le, le_rfl⟩ he)
    have hends' :
        (ray 0 = intrinsicAnnulusBoundary 1 (min p w) ∧
          ray s = intrinsicAnnulusBoundary 1 (max p w)) ∨
        (ray 0 = intrinsicAnnulusBoundary 1 (max p w) ∧
          ray s = intrinsicAnnulusBoundary 1 (min p w)) := by
      rcases le_total p w with h | h
      · rw [min_eq_left h, max_eq_right h]
        exact Or.inl ⟨h0, hpoint⟩
      · rw [min_eq_right h, max_eq_left h]
        exact Or.inr ⟨h0, hpoint⟩
    have hchildD : intrinsicBoundaryLength N.metric 1 (min p w) (max p w) ∈ D := by
      refine ⟨min p w, max p w, s, ray, W', Y', ?_, rfl⟩
      exact ⟨hlower, hac.trans (le_min hpC.1.le hw.1), min_lt_max.mpr hpw,
        (max_le hpC.2.le hw.2).trans hdb, hchild.trans hWU,
        hW', hY', hpY'.isConnected.isPreconnected, hbY', hd',
        by simpa only [hfW'] using hc', hfW'.trans hfY'.symm, hsub', hray,
        hslen.1, hslen.2, hsi, hends',
        fun t ht => (m64Intrinsic_open_region_strictly_inside_annulus hW hs _
          (hprefix t ht)).1, hrayGeo, hrayUnit0, hfW'⟩
    exact ⟨intrinsicBoundaryLength N.metric 1 (min p w) (max p w), hchildD,
      by simpa only [hL] using hloss⟩
  obtain ⟨L, hLD, hnear⟩ := exists_lt_of_csInf_lt hDnonempty
    (lt_add_of_pos_right (sInf D) (show 0 < q / 10 by positivity))
  obtain ⟨L', hL'D, hdecrease⟩ := hdescend L hLD
  have hinf : sInf D ≤ L' := csInf_le hDbdd hL'D
  linarith

end PoincareConjecture
