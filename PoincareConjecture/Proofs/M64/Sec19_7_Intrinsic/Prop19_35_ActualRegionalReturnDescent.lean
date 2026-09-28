import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ActualRegionalReturnStep












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_no_actual_regional_return
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
    False := by
  classical
  let P (c d Tc : ℝ) (gamma : ℝ → AnnulusCoordinates)
      (W Y : Set AnnulusCoordinates) : Prop :=
    r < intrinsicBoundaryLength N.metric 1 c d ∧
    a ≤ c ∧ c < d ∧ d ≤ b ∧ W ⊆ U ∧
    IsOpen W ∧ IsOpen Y ∧ IsPreconnected Y ∧
    ¬ Bornology.IsBounded Y ∧ Disjoint W Y ∧
    W ∪ Y = (frontier W)ᶜ ∧ frontier W = frontier Y ∧
    closure W ⊆ standardAnnulusDomain ∧
    ContDiff ℝ ∞ gamma ∧ 0 < Tc ∧ Tc < R ∧
    InjOn gamma (Icc 0 Tc) ∧
    ((gamma 0 = intrinsicAnnulusBoundary 1 c ∧
        gamma Tc = intrinsicAnnulusBoundary 1 d) ∨
      (gamma 0 = intrinsicAnnulusBoundary 1 d ∧
        gamma Tc = intrinsicAnnulusBoundary 1 c)) ∧
    (∀ t ∈ Ioo 0 Tc, 1 < ‖gamma t‖) ∧
    N.metric.IsGeodesicOn gamma (Icc 0 Tc) ∧
    N.metric.inner (gamma 0) (deriv gamma 0) (deriv gamma 0) = 1 ∧
    frontier W = intrinsicAnnulusBoundary 1 '' Icc c d ∪ gamma '' Icc 0 Tc
  let D : Set ℝ := {L | ∃ (c d Tc : ℝ) (gamma : ℝ → AnnulusCoordinates)
    (W Y : Set AnnulusCoordinates), P c d Tc gamma W Y ∧
      L = intrinsicBoundaryLength N.metric 1 c d}
  have hDnonempty : D.Nonempty := by
    refine ⟨intrinsicBoundaryLength N.metric 1 a b,
      a, b, T, beta, U, V, ?_, rfl⟩
    exact ⟨hlong, le_rfl, hab, le_rfl, Subset.rfl, hU, hV, hpV, hbV,
      hdisj, hcover, hfront, hsub, hbeta, hT, hTR, hbetaInj, hends,
      hbetaInside, hbetaGeo, hbetaUnit0, hfU⟩
  have hDbdd : BddBelow D := by
    refine ⟨r, ?_⟩
    rintro L ⟨c, d, Tc, gamma, W, Y, hP, rfl⟩
    exact hP.1.le
  have hdescend : ∀ L ∈ D, ∃ L' ∈ D, L' ≤ L - r / 10 := by
    rintro L ⟨c, d, Tc, gamma, W, Y, hP, hL⟩
    rcases hP with ⟨hlongC, hac, hcd, hdb, hWU, hW, hY, hpY, hbY, hd,
      hc, hf, hs, hg, hTc, hTcR, hgi, hge, hinside, hgg, hgu, hfW⟩
    have hparameters : Ioo c d ⊆ Ioo a b :=
      fun _ hp => ⟨hac.trans_lt hp.1, hp.2.trans_le hdb⟩
    have hperiodC : d - c < rampPeriod :=
      (sub_le_sub hdb hac).trans_lt hperiod
    obtain ⟨z, hz, w, hw, T', hT', hTR', _, _, hg', hgi', h0', h1', _,
        hgeo', hunit', _, _, _, _, hinside', W', Y', hW', hY', _, hpY',
        _, hbY', hd', hc', hfW', hfY', _, hW'W, _, hs', hlong', hloss⟩ :=
      m64Intrinsic_exists_actual_regional_return_step N
        hK hdelta hdeltaSmall hr hturn halpha hR hRshort hkappa hangle hRfocus
        harea hbudget hareaLoss hW hY hpY hbY hd hc hf hs hcd hperiodC hlongC
        hg hTc hTcR hgi hge hinside hgg hgu hfW e he normal annularHeight
        (fun p hp => hbase p (hparameters hp))
        (fun p hp => hderiv p (hparameters hp))
        (fun p hp => hunit0 p (hparameters hp))
        (fun p hp => horth p (hparameters hp))
        (fun p hp => hinward p (hparameters hp))
        (fun p hp => hAnn p (hparameters hp))
        (fun p hp => hgeo p (hparameters hp))
        (fun p hp => hmetric p (hparameters hp))
        (fun p hp hkp q hq hkq hpq hlength Tp Tq hTp hTpAnn hTpR
          hTq hTqAnn hTqR hprefixP hprefixQ hmeet =>
            hfocus p (hparameters hp) hkp q (hparameters hq) hkq hpq hlength
              Tp Tq hTp hTpAnn hTpR hTq hTqAnn hTqR
              (fun t ht => hWU (hprefixP t ht))
              (fun t ht => hWU (hprefixQ t ht)) hmeet)
    have hzw : z ≠ w := by
      intro heq
      have hsame : e !₂[z, 0] = e !₂[z, T'] :=
        h0'.trans ((congrArg (intrinsicAnnulusBoundary 1) heq).trans h1'.symm)
      exact hT'.ne (hgi' ⟨le_rfl, hT'.le⟩ ⟨hT'.le, le_rfl⟩ hsame)
    have hends' :
        (e !₂[z, 0] = intrinsicAnnulusBoundary 1 (min z w) ∧
          e !₂[z, T'] = intrinsicAnnulusBoundary 1 (max z w)) ∨
        (e !₂[z, 0] = intrinsicAnnulusBoundary 1 (max z w) ∧
          e !₂[z, T'] = intrinsicAnnulusBoundary 1 (min z w)) := by
      rcases le_total z w with h | h
      · rw [min_eq_left h, max_eq_right h]
        exact Or.inl ⟨h0', h1'⟩
      · rw [min_eq_right h, max_eq_left h]
        exact Or.inr ⟨h0', h1'⟩
    have hchild : intrinsicBoundaryLength N.metric 1 (min z w) (max z w) ∈ D := by
      refine ⟨min z w, max z w, T', (fun t => e !₂[z, t]), W', Y', ?_, rfl⟩
      refine ⟨hlong', hac.trans (le_min hz.1.le hw.1), min_lt_max.mpr hzw,
        (max_le hz.2.le hw.2).trans hdb, hW'W.trans hWU,
        hW', hY', hpY'.isConnected.isPreconnected, hbY', hd', ?_,
        hfW'.trans hfY'.symm, hs', hg', hT', hTR', hgi', hends', hinside',
        hgeo', hunit' 0 ⟨le_rfl, hT'.le⟩, hfW'⟩
      simpa only [hfW'] using hc'
    refine ⟨intrinsicBoundaryLength N.metric 1 (min z w) (max z w), hchild, ?_⟩
    simpa only [hL] using hloss
  obtain ⟨L, hLD, hLnear⟩ := exists_lt_of_csInf_lt hDnonempty
    (lt_add_of_pos_right (sInf D) (show 0 < r / 10 by positivity))
  obtain ⟨L', hL'D, hL'decrease⟩ := hdescend L hLD
  have hinf : sInf D ≤ L' := csInf_le hDbdd hL'D
  linarith

end PoincareConjecture
