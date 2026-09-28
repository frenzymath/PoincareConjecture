import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMixedEnds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseCapCaller
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseCapTransfer
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsBallModel









set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D


theorem exists_ball_of_morse_disc_and_saved_cap
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (C : SurgeryCapTag psi u)
    (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source)
    (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (c kappa rho : ℝ) (hkappa : |kappa| = 1) (hrho : 0 < rho)
    (hCsign : C.sign = -kappa)
    (hsource : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source)
    (hheight : ∀ p ∈ A.source, ⟪(u : E3), A p⟫_ℝ = p.2)
    (hgraph : ∀ p ∈ A.source,
      A p ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        p.2 = c + kappa * ‖p.1‖ ^ 2)
    (K : Set E3) (hK : IsCompact K) :
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    let original : E2 → E3 := fun x => A (x, c + kappa * ‖x‖ ^ 2)
    let discOpen : Set E3 := original '' ball (0 : E2) rho
    let s : ℝ := c + kappa * rho ^ 2
    let t : ℝ := C.cutHeight + C.sign * C.removal
    let ell : ℝ := min s t
    let upper : ℝ := max s t
    0 < kappa * (t - s) →
    K = {y : E3 | y ∈ S ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} →
    S \ discOpen = K ∪ C.cap →
    ∀ eta : ℝ, 0 < eta →
    ∀ gamma : ℝ → UnitCircle → E2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => gamma p.1 p.2) →
      (∀ z ∈ Icc (ell - eta) (upper + eta),
        IsPlanarEmbedding (gamma z)) →
      (∀ z ∈ Icc (ell - eta) (upper + eta),
        range (gamma z) = {x : E2 |
          (heightPlaneCoordinates u).symm (x, z) ∈ S}) →
      ∃ B : BallNeighborhoodChart E3 E3,
        B.boundary = S ∧
        B.boundary = psi '' ((univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ)) := by
  classical
  intro S original discOpen s t ell upper horder hKband hrest eta heta gamma hc hce hfull
  have hkcases : kappa = 1 ∨ kappa = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using hkappa
  have hpositive (hk : kappa = 1) : ell = s ∧ upper = t := by
    have hst : s < t := by rw [hk, one_mul] at horder; linarith only [horder]
    exact ⟨min_eq_left hst.le, max_eq_right hst.le⟩
  have hnegative (hk : kappa ≠ 1) : ell = t ∧ upper = s := by
    have hk' := hkcases.resolve_left hk
    have hts : t < s := by rw [hk', neg_one_mul] at horder; linarith only [horder]
    exact ⟨min_eq_right hts.le, max_eq_left hts.le⟩
  have hlt : ell < upper := by
    by_cases hk : kappa = 1
    · rw [(hpositive hk).1, (hpositive hk).2]
      rw [hk, one_mul] at horder
      linarith only [horder]
    · rw [(hnegative hk).1, (hnegative hk).2]
      rw [hkcases.resolve_left hk, neg_one_mul] at horder
      linarith only [horder]
  obtain ⟨epsilon, delta, he, heeta, _herho, _heoverlap, _hsep, hd, _hdquarter,
      RM, RC, T, Q, hTs, _hTt, hTv, _hTinv, hT, hTi, hTh, _hTih,
      hTfilled, hQ, hQi, hQh, _hQih, hQsource, hmatchM, hmatchC, hcore⟩ :=
    exists_stackMorseCapMatchedChart hP psi u C A hA hAi c kappa rho hkappa hrho
      hsource hheight hgraph horder eta heta gamma hc hce hfull
  obtain ⟨rFlat, rOne, v0, v1, hrFlat, hrann, hradii, hrOne, hv0, hv01, hv1, hgap⟩ :=
    exists_stackCanonicalRadii delta hd
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let lambdaM := min (epsilon / 2) (rho ^ 2 / 2) / 2
  have hmin : 0 < min (epsilon / 2) (rho ^ 2 / 2) :=
    lt_min (by linarith only [he]) (div_pos (sq_pos_of_pos hrho) (by norm_num))
  have hlM : 0 < lambdaM := div_pos hmin (by norm_num)
  have hlMe : lambdaM < epsilon / 2 := by
    have hh := min_le_left (epsilon / 2) (rho ^ 2 / 2)
    dsimp only [lambdaM]
    linarith only [hmin, hh]
  have hlMr : lambdaM < rho ^ 2 / 2 := by
    have hh := min_le_right (epsilon / 2) (rho ^ 2 / 2)
    dsimp only [lambdaM]
    linarith only [hmin, hh]
  let distance := fun q : UnitTwoSphere =>
    rho ^ 2 + lambdaM * (M (heightCoordinates (q : E3))).2
  let endpoint := fun q : UnitTwoSphere =>
    A (Real.sqrt (distance q) • (M (heightCoordinates (q : E3))).1,
      c + kappa * distance q)
  let disc := original '' closedBall (0 : E2) rho
  let L := endpoint '' Qminus
  obtain ⟨_r0, _hr0, _hr0rho, Phi, _support, N, horiginal, _hhorizontal,
      _hendpoints, _hPhi, _hPhii, _hPhi0, _htrack, _hcompact, _hsupport,
      _hs, _hsi, hN, hrestN, _hdisjoint, hfix, _hdiscS, _hdiscBoundary,
      hFMdisc, _hFMinverse, _hcross, hFMsurface, hLheight, _hflat, _hFlatL⟩ :=
    exists_stackMorseCanonicalCapNormalization psi u A hA hAi c kappa rho lambdaM
      hkappa hrho hlM hlMr hsource hheight hgraph
      rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  let FM := Phi 1
  change FM '' disc = L at hFMdisc
  change FM '' S = (S \ discOpen) ∪ L at hFMsurface
  change S \ discOpen ⊆ N at hrestN
  change ∀ y ∈ L, -lambdaM ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
    kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ 0 at hLheight
  have hCN : C.cap ⊆ N := by
    intro y hy
    exact hrestN (hrest.symm ▸ Or.inr hy)
  obtain ⟨C1, _hC1profile, hC1tube, hC1cut, hC1rem, hC1sign, _hC1scale,
      _hC1beta, _hC1sourceChart, _hC1flatChart, _hC1overlap, _hC1collar,
      _hC1sourceCap, _hC1sourceSeam, hC1cap, hC1seam⟩ :=
    exists_stackCapTag_transport_of_fixed_neighborhood C FM N hN hCN
      (fun y hy => (hfix 1 y hy).1)
  have hpsi1 : IsCollarEmbedding (fun p => FM (psi p)) := by
    refine ⟨FM.contMDiff.comp_contMDiffOn hpsi.1, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hpsi.2.1 hx hy (FM.injective hxy)
    · intro p hp
      have hdpsi := (hpsi.1.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp)).mdifferentiableAt (by simp)
      have hdFM := (FM.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
        (x := psi p) (mem_univ _)
      change Function.Injective
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ((FM : E3 → E3) ∘ psi) p)
      rw [mfderiv_comp p (FM.mdifferentiable (by simp) (psi p)) hdpsi]
      exact hdFM.comp (hpsi.2.2 p hp)
  have hgraphCont : Continuous (fun x : E2 => (x, c + kappa * ‖x‖ ^ 2)) :=
    continuous_id.prodMk (continuous_const.add (continuous_const.mul (continuous_norm.pow 2)))
  have hdiscCompact : IsCompact disc :=
    (isCompact_closedBall (0 : E2) rho).image_of_continuousOn
      (hA.continuousOn.comp hgraphCont.continuousOn horiginal)
  have hL : IsCompact L := hFMdisc ▸ hdiscCompact.image FM.continuous
  let H := (heightPlaneCoordinates u).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  let YM := (fun q : UnitTwoSphere =>
    (s + kappa * lambdaM * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  have hQs (z : ℝ) (hz : z ∈ Icc ell upper) :
      Icc (z - epsilon) (z + epsilon) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source := by
    intro p hp
    apply hQsource
    exact ⟨⟨by linarith only [hp.1.1, hz.1, heeta, he],
      by linarith only [hp.1.2, hz.2, heeta, he]⟩, hp.2⟩
  have hsBand : s ∈ Icc ell upper := ⟨min_le_left _ _, le_max_left _ _⟩
  have htBand : t ∈ Icc ell upper := ⟨min_le_right _ _, le_max_right _ _⟩
  have hTsmall : Icc (s - epsilon) (s + epsilon) ×ˢ
      closedBall (0 : E2) 1 ⊆ T.source := by
    intro p hp
    apply hTfilled
    exact ⟨⟨by linarith only [hp.1.1, he], by linarith only [hp.1.2, he]⟩, hp.2⟩
  obtain ⟨_hYMT, _hYMQ, _hrot, _hHT, _hTQ, _hHTtarget, _hHQtarget,
      hLimage, _hQinverse, _hFlatY, _hFlatImage, _hPhysicalFlat, _hFlatCap, _hFlatSource⟩ :=
    stackMorseCanonicalCap_image_eq_of_annular_match u A RM T Q hT hTi hQ hQi hTh hQh
      c kappa rho lambdaM epsilon delta hkappa hrho hlM hlMr
      (by linarith only [hlMe, he]) hd hTs hTv hTsmall (hQs s hsBand)
      (fun z hz x hx => (hmatchM z hz x hx).2)
      rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  change L = H.symm '' (Q '' YM) at hLimage
  have hCseamS : C.seam ⊆ S := by
    rintro y ⟨q, _hq, rfl⟩
    exact mem_range_self q
  have hCseamHeight (y : E3) (hy : y ∈ C.seam) : ⟪(u : E3), y⟫_ℝ = t := by
    obtain ⟨q, hq, rfl⟩ := C.seam_eq_image ▸ hy
    have hzero : (C.profile.model q).2 = 0 := by
      change C.profile.vertical
        (C.profile.horizontal (heightCoordinates (q : E3)).2 •
          (heightCoordinates (q : E3)).1) * (heightCoordinates (q : E3)).2 = 0
      rw [hq, mul_zero]
    have hsourceq : ((C.profile.model q).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2)) ∈
        C.tube.source :=
      C.tube_source ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q), mem_univ _⟩
    rw [SurgeryCapProfile.capMap_apply, C.tube_height _ hsourceq, hzero]
    simp only [mul_zero, add_zero]
    rfl
  have hseam : C1.seam ⊆ K := by
    rw [hC1seam]
    intro y hy
    rw [hKband]
    refine ⟨hCseamS hy, ?_⟩
    rw [hCseamHeight y hy]
    exact htBand
  have hKside : ∀ y ∈ K,
      0 ≤ C1.sign * (⟪(u : E3), y⟫_ℝ - (C1.cutHeight + C1.sign * C1.removal)) := by
    intro y hy
    have hb := (hKband ▸ hy).2
    rw [hC1sign, hC1cut, hC1rem]
    change 0 ≤ C.sign * (⟪(u : E3), y⟫_ℝ - t)
    rw [hCsign]
    by_cases hk : kappa = 1
    · rw [(hpositive hk).2] at hb
      rw [hk]
      linarith only [hb.2]
    · rw [(hnegative hk).1] at hb
      rw [hkcases.resolve_left hk]
      linarith only [hb.1]
  have hLside : ∀ y ∈ L, kappa * (t - s) ≤
      C1.sign * (⟪(u : E3), y⟫_ℝ - (C1.cutHeight + C1.sign * C1.removal)) := by
    intro y hy
    have hh := (hLheight y hy).2
    rw [hC1sign, hC1cut, hC1rem]
    change kappa * (t - s) ≤ C.sign * (⟪(u : E3), y⟫_ℝ - t)
    rw [hCsign]
    nlinarith only [hh]
  have hcover1 : range (fun q : UnitTwoSphere => FM (psi (q, 0))) = K ∪ C1.cap ∪ L := by
    rw [hC1cap, ← hrest, range_comp']
    exact hFMsurface
  have hC1Qs : Icc (C1.cutHeight + C1.sign * C1.removal - epsilon)
      (C1.cutHeight + C1.sign * C1.removal + epsilon) ×ˢ
        closedBall (0 : E2) 1 ⊆ Q.source := by
    rw [hC1cut, hC1sign, hC1rem]
    exact hQs t htBand
  have hC1match : ∀ z ∈ Icc (C1.cutHeight + C1.sign * C1.removal - epsilon)
      (C1.cutHeight + C1.sign * C1.removal + epsilon), ∀ x : E2,
      |‖x‖ - 1| < delta → stackCapEndChart C1 RC (z, x) = Q (z, x) := by
    rw [hC1cut, hC1sign, hC1rem]
    intro z hz x hx
    have htubes : stackCapEndChart C1 RC (z, x) = stackCapEndChart C RC (z, x) := by
      change H (C1.tube (RC x, z)) = H (C.tube (RC x, z))
      rw [hC1tube]
    exact htubes.trans (hmatchC z hz x hx).2
  obtain ⟨lambdaC, hlC, _hlCscale, hlCe, FC, NC, _hpsiFinal, _hNC,
      _hLNC, _hFCfix, _hFCK, _hFCiK, _hFCseam, _hFCtrack,
      _hYCs, _hFCcap, _hFCicap, _hKcap, _hcapL, hFcover⟩ :=
    exists_stackCapNormalization_in_matched_chart C1 hpsi1 K L hK hL
      (kappa * (t - s)) horder hcover1 hseam hKside hLside RC Q hQ hQi hQh
      epsilon delta he hd hC1Qs hC1match
      rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  let YC := (fun q : UnitTwoSphere =>
    (t + C.sign * lambdaC * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let LC := H.symm '' (Q '' YC)
  let F := FM.trans FC
  simp only [hC1cut, hC1sign, hC1rem] at hFcover
  change range (fun q : UnitTwoSphere => F (psi (q, 0))) = K ∪ LC ∪ L at hFcover
  let lm := if kappa = 1 then lambdaM else lambdaC
  let lp := if kappa = 1 then lambdaC else lambdaM
  have hlm : 0 < lm := by
    by_cases hk : kappa = 1 <;> simp only [lm, hk, ite_true, ite_false] <;> assumption
  have hlp : 0 < lp := by
    by_cases hk : kappa = 1 <;> simp only [lp, hk, ite_true, ite_false] <;> assumption
  have hlme : lm < epsilon / 2 := by
    by_cases hk : kappa = 1 <;> simp only [lm, hk, ite_true, ite_false] <;> assumption
  have hlpe : lp < epsilon / 2 := by
    by_cases hk : kappa = 1 <;> simp only [lp, hk, ite_true, ite_false] <;> assumption
  let Ylo := (fun q : UnitTwoSphere =>
    (ell + lm * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let Yup := (fun q : UnitTwoSphere =>
    (upper - lp * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  have hposCaps (hk : kappa = 1) : Ylo = YM ∧ Yup = YC := by
    simp only [Ylo, Yup, YM, YC, lm, lp, if_pos hk, (hpositive hk).1,
      (hpositive hk).2, hCsign, hk, one_mul, neg_mul, sub_eq_add_neg, and_self]
  have hnegCaps (hk : kappa ≠ 1) : Ylo = YC ∧ Yup = YM := by
    simp only [Ylo, Yup, YM, YC, lm, lp, if_neg hk, (hnegative hk).1,
      (hnegative hk).2, hCsign, hkcases.resolve_left hk, neg_neg, one_mul,
      neg_mul, sub_eq_add_neg, and_self]
  change H.symm '' (Q '' (Icc ell upper ×ˢ sphere (0 : E2) 1)) =
    {y : E3 | y ∈ S ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} at hcore
  have hcoreK : H.symm '' (Q '' (Icc ell upper ×ˢ sphere (0 : E2) 1)) = K :=
    hcore.trans hKband.symm
  obtain ⟨_g, _hg, _hgpos, _hgsurj, _hglo, _hghi, D0, _hD0, hsolid,
      B0, hB0chart, hB0boundary⟩ :=
    exists_stackCanonicalBallModel ell upper lm lp hlt hlm hlp
      rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  change B0.boundary = Ylo ∪ (Icc ell upper ×ˢ sphere (0 : E2) 1) ∪ Yup at hB0boundary
  let E := B0.chart.trans Q
  have hEs : closedBall (0 : E3) 1 ⊆ E.source := by
    intro x hx
    refine ⟨B0.closedBall_subset_source hx, ?_⟩
    have hb : D0 x ∈ Icc (ell - lm) (upper + lp) ×ˢ closedBall (0 : E2) 1 :=
      hsolid (mem_image_of_mem D0 hx)
    change B0.chart x ∈ Q.source
    rw [hB0chart]
    apply hQsource
    refine ⟨⟨?_, ?_⟩, hb.2⟩
    · change ell - eta ≤ (D0 x).1
      linarith only [hb.1.1, hlme, heeta, he]
    · change (D0 x).1 ≤ upper + eta
      linarith only [hb.1.2, hlpe, heeta, he]
  have hE : ContDiffOn ℝ ∞ E E.source :=
    hQ.comp (B0.smooth.mono inter_subset_left) (fun _ hx => hx.2)
  have hEi : ContDiffOn ℝ ∞ E.symm E.target :=
    B0.smooth_symm.comp (hQi.mono inter_subset_left) (fun _ hx => hx.2)
  let V := (E.transHomeomorph H.symm.toHomeomorph).transHomeomorph F.symm.toHomeomorph
  have hV : ContDiffOn ℝ ∞ V V.source :=
    F.symm.contDiff.comp_contDiffOn (H.symm.contDiff.comp_contDiffOn hE)
  have hVi : ContDiffOn ℝ ∞ V.symm V.target :=
    hEi.comp (H.contDiff.comp F.contDiff).contDiffOn (fun _ hy => hy)
  let B : BallNeighborhoodChart E3 E3 := ⟨V, hEs, hV, hVi⟩
  have hboundary : B.boundary = F.symm '' (H.symm '' (Q '' B0.boundary)) := by
    change (fun x => F.symm (H.symm (Q (B0.chart x)))) '' sphere (0 : E3) 1 =
      F.symm '' (H.symm '' (Q '' (B0.chart '' sphere (0 : E3) 1)))
    rw [image_image, image_image, image_image]
  have hnormalizedBoundary : H.symm '' (Q '' B0.boundary) = K ∪ LC ∪ L := by
    rw [hB0boundary]
    simp only [image_union]
    by_cases hk : kappa = 1
    · rw [(hposCaps hk).1, (hposCaps hk).2, hcoreK, ← hLimage]
      change L ∪ K ∪ LC = K ∪ LC ∪ L
      ac_rfl
    · rw [(hnegCaps hk).1, (hnegCaps hk).2, hcoreK, ← hLimage]
      change LC ∪ K ∪ L = K ∪ LC ∪ L
      ac_rfl
  have hfinal : B.boundary = S := by
    rw [hboundary, hnormalizedBoundary, ← hFcover, ← range_comp']
    simp only [Diffeomorph.symm_apply_apply]
    rfl
  refine ⟨B, hfinal, hfinal.trans ?_⟩
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨⟨q, z⟩, ⟨_, hz⟩, rfl⟩
    have hz' : z = 0 := hz
    subst z
    exact ⟨q, rfl⟩

end PoincareConjecture.M25.Topology3D
