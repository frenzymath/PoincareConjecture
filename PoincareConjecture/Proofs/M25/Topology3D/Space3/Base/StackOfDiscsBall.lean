import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTwoEnds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTwoCaps
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsBallModel

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

theorem exists_ball_of_classified_two_caps
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (Cm Cp : SurgeryCapTag psi u)
    (hCm : Cm.sign = 1) (hCp : Cp.sign = -1)
    (K : Set E3)
    (hcover : range (fun q : UnitTwoSphere => psi (q, 0)) = K ∪ Cm.cap ∪ Cp.cap)
    (hm : K ∩ Cm.cap = Cm.seam) (hp : K ∩ Cp.cap = Cp.seam)
    (hdisjoint : Disjoint Cm.cap Cp.cap)
    (horder : Cm.cutHeight + Cm.sign * Cm.removal <
      Cp.cutHeight + Cp.sign * Cp.removal)
    (hheight : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ∈
      Icc (Cm.cutHeight + Cm.sign * Cm.removal)
        (Cp.cutHeight + Cp.sign * Cp.removal))
    (hreg : ∀ q : UnitTwoSphere, psi (q, 0) ∈ K →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ B : BallNeighborhoodChart E3 E3,
      B.boundary = range (fun q : UnitTwoSphere => psi (q, 0)) ∧
      B.boundary = psi '' ((univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ)) := by
  obtain ⟨_hKsource, hK, _hKconnected, hKband, eta, heta, c, hc, hce, hfull⟩ :=
    exists_stackCircleFamily_of_two_caps psi hpsi u Cm Cp hCm hCp K hcover hm hp
      hdisjoint horder hheight hreg
  let ell := Cm.cutHeight + Cm.sign * Cm.removal
  let r := Cp.cutHeight + Cp.sign * Cp.removal
  obtain ⟨epsilon, delta, hepsilon, heeta, _hsep, hdelta, _hdquarter,
      Rm, Rp, _hRm, _hRp, cbar, _hcb, _hcbe, hrange, _hout, D, G,
      PhiM, PhiP, Sm, Sp, hmatched⟩ :=
    exists_stackTwoCapMatchedChart Cm Cp horder hP eta heta c hc hce hfull
  let Qm := PhiM.toHomeomorph.toOpenPartialHomeomorph.trans G.chart
  let Q := PhiP.toHomeomorph.toOpenPartialHomeomorph.trans Qm
  obtain ⟨_hSm, _hSp, _hSmheight, _hSpheight, _hMs, _hMis, _hPs, _hPis,
      _hMfix, _hPfix, _hPhih, _hcircle, _hPfixm, _hMfixp, _hQs, _hQt,
      hQ, hQi, hQh, _hQih, hQsource, _hQproduct, hQcircle, hmatchm, hmatchp⟩ := hmatched
  obtain ⟨rFlat, rOne, v0, v1, hrFlat, hrann, hradii, hrOne, hv0, hv01, hv1, hgap⟩ :=
    exists_stackCanonicalRadii delta hdelta
  have hsm : Cm.seam ⊆ K := by rw [← hm]; exact inter_subset_left
  have hsp : Cp.seam ⊆ K := by rw [← hp]; exact inter_subset_left
  have hQs : Icc (ell - epsilon) (r + epsilon) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source := by
    intro p hp
    apply hQsource
    exact ⟨⟨by linarith only [hp.1.1, heeta], by linarith only [hp.1.2, heeta]⟩, hp.2⟩
  obtain ⟨lm, lp, hlm, _hlmscale, hlmsmall, hlp, _hlpscale, hlpsmall,
      Fm, Cp1, Fp, Nm, Np, hnormalized⟩ :=
    exists_stackTwoCapCanonicalNormalization Cm Cp hpsi hCm hCp K hK hcover hsm hsp
      horder hheight Q hQ hQi hQh Rm Rp epsilon delta hepsilon hdelta hQs
      (fun z hz x hx => (hmatchm z hz x hx).2.symm)
      (fun z hz x hx => (hmatchp z hz x hx).2.symm)
      rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let Ym := (fun q : UnitTwoSphere =>
    (ell + lm * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let Yp := (fun q : UnitTwoSphere =>
    (r - lp * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let H := (heightPlaneCoordinates u).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  let Lm := H.symm '' (Q '' Ym)
  let Lp := H.symm '' (Q '' Yp)
  let F := Fm.trans Fp
  obtain ⟨_hprofile, _htube, _hcut, _hrem, _hsign, _hscale, _hbeta,
      _hsourceChart, _hflatChart, _hoverlap, _hcollar, _hsourceCap, _hsourceSeam,
      _hcap, _hseam, _hpsim, _hpsiF, _hNm, _hCpNm, _hFmfix,
      _hNp, _hLmNp, _hFpfix, _hFmK, _hFmiK, _hFpK, _hFpiK, _hFK, _hFiK,
      _hYms, _hYps, _hFmcap, _hFpLm, _hFpiLm, _hFCm, _hFCp, _hFiLm, _hFiLp,
      _hFseam, _hFmtrack, _hFptrack, _htrackm, _htrackp, _hKcm, _hKcp,
      _hdisjoint, hFcover⟩ := hnormalized
  change range (fun q : UnitTwoSphere => F (psi (q, 0))) = K ∪ Lm ∪ Lp at hFcover
  have hband (z : ℝ) (hz : z ∈ Icc ell r) : z ∈ Icc (ell - eta) (r + eta) := by
    constructor <;> linarith only [hz.1, hz.2, heta]
  have hlevels (z : ℝ) (hz : z ∈ Icc ell r) :
      range (cbar z) = {x : E2 | H.symm (z, x) ∈
        range (fun q : UnitTwoSphere => psi (q, 0))} :=
    (hrange z).trans (hfull z (hband z hz))
  have hgraph (z : ℝ) (hz : z ∈ Icc ell r) (q : UnitCircle) :
      Q (z, (q : E2)) = (z, cbar z q) := by
    rw [hQcircle z q q.property, G.chart_apply, D.chart_boundary z (hband z hz) q]
  have hHheight (p : P) : ⟪(u : E3), H.symm p⟫_ℝ = p.1 := by
    rw [← heightPlaneCoordinates_snd]
    exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (p.2, p.1))
  let Z := Icc ell r ×ˢ sphere (0 : E2) 1
  have hcore : H.symm '' (Q '' Z) = K := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨z, x⟩, ⟨hz, hx⟩, rfl⟩, rfl⟩
      rw [hgraph z hz ⟨x, hx⟩, hKband]
      refine ⟨?_, ?_⟩
      · change cbar z ⟨x, hx⟩ ∈ {x : E2 | H.symm (z, x) ∈
          range (fun q : UnitTwoSphere => psi (q, 0))}
        rw [← hlevels z hz]
        exact ⟨(⟨x, hx⟩ : UnitCircle), rfl⟩
      · rw [hHheight]
        exact hz
    · intro y hy
      let z := ⟪(u : E3), y⟫_ℝ
      let x := (heightPlaneCoordinates u y).1
      have hz : z ∈ Icc ell r := hheight y hy
      have hrepr : H.symm (z, x) = y := heightPlaneCoordinates_reconstruct u y z rfl
      have hx : x ∈ range (cbar z) := by
        rw [hlevels z hz]
        change H.symm (z, x) ∈ range (fun q : UnitTwoSphere => psi (q, 0))
        rw [hrepr]
        exact (hKband ▸ hy).1
      obtain ⟨q, hq⟩ := hx
      refine ⟨Q (z, (q : E2)), ⟨(z, (q : E2)), ⟨hz, q.property⟩, rfl⟩, ?_⟩
      rw [hgraph z hz q, hq]
      exact hrepr
  obtain ⟨_g, _hg, _hgpos, _hgsurj, _hglo, _hghi, D0, _hD0, hsolid, B0,
      hB0chart, hB0boundary⟩ :=
    exists_stackCanonicalBallModel ell r lm lp horder hlm hlp
      rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  let E := B0.chart.trans Q
  have hEs : closedBall (0 : E3) 1 ⊆ E.source := by
    intro x hx
    refine ⟨B0.closedBall_subset_source hx, ?_⟩
    have hb := hsolid (mem_image_of_mem D0 hx)
    change B0.chart x ∈ Q.source
    rw [hB0chart]
    apply hQs
    refine ⟨⟨?_, ?_⟩, hb.2⟩
    · change ell - epsilon ≤ (D0 x).1
      linarith only [hb.1.1, hlmsmall, hepsilon]
    · change (D0 x).1 ≤ r + epsilon
      linarith only [hb.1.2, hlpsmall, hepsilon]
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
  have hnormalizedBoundary : H.symm '' (Q '' B0.boundary) = Lm ∪ K ∪ Lp := by
    rw [hB0boundary]
    simp only [image_union]
    rw [hcore]
  have hfinal : B.boundary = range (fun q : UnitTwoSphere => psi (q, 0)) := by
    rw [hboundary, hnormalizedBoundary, union_comm Lm K, ← hFcover, ← range_comp']
    simp only [Diffeomorph.symm_apply_apply]
  refine ⟨B, hfinal, hfinal.trans ?_⟩
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    have ht' : t = 0 := ht
    subst t
    exact ⟨q, rfl⟩

end PoincareConjecture.M25.Topology3D
