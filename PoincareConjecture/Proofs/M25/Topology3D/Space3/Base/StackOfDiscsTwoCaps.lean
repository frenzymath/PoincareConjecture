import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapTransfer
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsLevels

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

theorem exists_stackTwoCapCanonicalNormalization
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (Cm Cp : SurgeryCapTag psi u) (hpsi : IsCollarEmbedding psi)
    (hCm : Cm.sign = 1) (hCp : Cp.sign = -1)
    (K : Set E3) (hK : IsCompact K)
    (hcover : range (fun q : UnitTwoSphere => psi (q, 0)) = K ∪ Cm.cap ∪ Cp.cap)
    (hsm : Cm.seam ⊆ K) (hsp : Cp.seam ⊆ K)
    (horder : Cm.cutHeight + Cm.sign * Cm.removal <
      Cp.cutHeight + Cp.sign * Cp.removal)
    (hheight : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ∈
      Icc (Cm.cutHeight + Cm.sign * Cm.removal)
        (Cp.cutHeight + Cp.sign * Cp.removal))
    (Q : OpenPartialHomeomorph P P)
    (hQ : ContDiffOn ℝ ∞ Q Q.source)
    (hQi : ContDiffOn ℝ ∞ Q.symm Q.target)
    (hQh : ∀ p ∈ Q.source, (Q p).1 = p.1)
    (Rm Rp : E2 ≃ₗᵢ[ℝ] E2)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hQs : Icc (Cm.cutHeight + Cm.sign * Cm.removal - epsilon)
      (Cp.cutHeight + Cp.sign * Cp.removal + epsilon) ×ˢ closedBall (0 : E2) 1
        ⊆ Q.source)
    (hmatchm : ∀ z ∈ Icc (Cm.cutHeight + Cm.sign * Cm.removal - epsilon)
      (Cm.cutHeight + Cm.sign * Cm.removal + epsilon), ∀ x : E2,
      |‖x‖ - 1| < delta → stackCapEndChart Cm Rm (z, x) = Q (z, x))
    (hmatchp : ∀ z ∈ Icc (Cp.cutHeight + Cp.sign * Cp.removal - epsilon)
      (Cp.cutHeight + Cp.sign * Cp.removal + epsilon), ∀ x : E2,
      |‖x‖ - 1| < delta → stackCapEndChart Cp Rp (z, x) = Q (z, x))
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hrann : 1 - delta < rFlat)
    (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hprofileGap : v1 ^ 2 + rOne ^ 2 < 1) :
    let ell := Cm.cutHeight + Cm.sign * Cm.removal
    let r := Cp.cutHeight + Cp.sign * Cp.removal
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let Hinv := fun p : P => (heightPlaneCoordinates u).symm (p.2, p.1)
    ∃ lm lp : ℝ, 0 < lm ∧ lm < Cm.scale ∧ lm < epsilon / 2 ∧
      0 < lp ∧ lp < Cp.scale ∧ lp < epsilon / 2 ∧
      ∃ Fm : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        ∃ Cp1 : SurgeryCapTag (fun p => Fm (psi p)) u,
          ∃ Fp : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
            ∃ Nm Np : Set E3,
              let F := Fm.trans Fp
              let Ym := (fun q : UnitTwoSphere =>
                (ell + lm * (M (heightCoordinates (q : E3))).2,
                  (M (heightCoordinates (q : E3))).1)) '' Qminus
              let Yp := (fun q : UnitTwoSphere =>
                (r - lp * (M (heightCoordinates (q : E3))).2,
                  (M (heightCoordinates (q : E3))).1)) '' Qminus
              let Lm := Hinv '' (Q '' Ym)
              let Lp := Hinv '' (Q '' Yp)
              Cp1.profile = Cp.profile ∧ Cp1.tube = Cp.tube ∧
              Cp1.cutHeight = Cp.cutHeight ∧ Cp1.removal = Cp.removal ∧
              Cp1.sign = Cp.sign ∧ Cp1.scale = Cp.scale ∧ Cp1.beta = Cp.beta ∧
              Cp1.sourceChart = Cp.sourceChart ∧ Cp1.flatChart = Cp.flatChart ∧
              Cp1.overlapWidth ≤ Cp.overlapWidth ∧ Cp1.collarWidth ≤ Cp.collarWidth ∧
              Cp1.sourceCap = Cp.sourceCap ∧ Cp1.sourceSeam = Cp.sourceSeam ∧
              Cp1.cap = Cp.cap ∧ Cp1.seam = Cp.seam ∧
              IsCollarEmbedding (fun p => Fm (psi p)) ∧
              IsCollarEmbedding (fun p => F (psi p)) ∧
              IsOpen Nm ∧ Cp.cap ⊆ Nm ∧
              (∀ y ∈ Nm, Fm y = y ∧ Fm.symm y = y) ∧
              IsOpen Np ∧ Lm ⊆ Np ∧
              (∀ y ∈ Np, Fp y = y ∧ Fp.symm y = y) ∧
              Fm '' K = K ∧ Fm.symm '' K = K ∧
              Fp '' K = K ∧ Fp.symm '' K = K ∧
              F '' K = K ∧ F.symm '' K = K ∧
              Ym ⊆ Q.source ∧ Yp ⊆ Q.source ∧
              Fm '' Cm.cap = Lm ∧ Fp '' Lm = Lm ∧ Fp.symm '' Lm = Lm ∧
              F '' Cm.cap = Lm ∧ F '' Cp.cap = Lp ∧
              F.symm '' Lm = Cm.cap ∧ F.symm '' Lp = Cp.cap ∧
              (∀ y ∈ Cm.seam ∪ Cp.seam, F y = y ∧ F.symm y = y) ∧
              (∀ q ∈ Qminus,
                Fm (Cm.profile.capMap Cm.tube Cm.cutHeight Cm.sign Cm.removal Cm.scale q) =
                  stackCapCanonicalEndpoint Cm rFlat rOne v0 v1 lm q) ∧
              (∀ q ∈ Qminus,
                Fp (Cp1.profile.capMap Cp1.tube Cp1.cutHeight Cp1.sign
                  Cp1.removal Cp1.scale q) =
                    stackCapCanonicalEndpoint Cp1 rFlat rOne v0 v1 lp q) ∧
              (∀ q ∈ Qminus,
                F (Cm.profile.capMap Cm.tube Cm.cutHeight Cm.sign Cm.removal Cm.scale q) =
                  stackCapCanonicalEndpoint Cm rFlat rOne v0 v1 lm q) ∧
              (∀ q ∈ Qminus,
                F (Cp.profile.capMap Cp.tube Cp.cutHeight Cp.sign Cp.removal Cp.scale q) =
                  stackCapCanonicalEndpoint Cp rFlat rOne v0 v1 lp q) ∧
              K ∩ Lm = Cm.seam ∧ K ∩ Lp = Cp.seam ∧ Disjoint Lm Lp ∧
              range (fun q : UnitTwoSphere => F (psi (q, 0))) = K ∪ Lm ∪ Lp := by
  let ell := Cm.cutHeight + Cm.sign * Cm.removal
  let r := Cp.cutHeight + Cp.sign * Cp.removal
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let Hinv := fun p : P => (heightPlaneCoordinates u).symm (p.2, p.1)
  have hlr : ell < r := horder
  have hKminus (y : E3) (hy : y ∈ K) :
      0 ≤ Cm.sign * (⟪(u : E3), y⟫_ℝ - ell) := by
    rw [hCm, one_mul]
    exact sub_nonneg.mpr (hheight y hy).1
  have hLminus (y : E3) (hy : y ∈ Cp.cap) :
      r - ell ≤ Cm.sign * (⟪(u : E3), y⟫_ℝ - ell) := by
    have hh := (Cp.cap_seam_signed_height y hy).1
    change Cp.sign * (⟪(u : E3), y⟫_ℝ - r) ≤ 0 at hh
    rw [hCp, neg_one_mul] at hh
    rw [hCm, one_mul]
    linarith only [hh]
  have hQsm : Icc (ell - epsilon) (ell + epsilon) ×ˢ closedBall (0 : E2) 1 ⊆
      Q.source := by
    intro p hp
    apply hQs
    exact ⟨⟨hp.1.1, by linarith only [hp.1.2, hlr]⟩, hp.2⟩
  obtain ⟨lm, hlm, hlmscale, hlmsmall, Fm, Nm, hpsim, hNm, hCpNm, hFmfix,
      hFmK, hFmiK, hFmseam, hFmtrack, hYms, hFmcap, hFmicap, hKcm, _hLmCp, hcoverm⟩ :=
    exists_stackCapNormalization_in_matched_chart Cm hpsi K Cp.cap hK Cp.cap_isCompact
      (r - ell) (sub_pos.mpr hlr) hcover hsm hKminus hLminus Rm Q hQ hQi hQh
      epsilon delta hepsilon hdelta hQsm hmatchm rFlat rOne v0 v1
      hrFlat hrann hradii hrOne hv0 hv01 hv1 hprofileGap
  let Ym := (fun q : UnitTwoSphere =>
    (ell + lm * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let Lm := Hinv '' (Q '' Ym)
  have hYm : (fun q : UnitTwoSphere =>
      (ell + Cm.sign * lm * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus = Ym := by
    simp only [Ym, hCm, one_mul]
  rw [hYm] at hYms hFmcap hFmicap hKcm _hLmCp hcoverm
  obtain ⟨Cp1, hprofile, htube, hcut, hrem, hsign, hscale, hbeta,
      hsourceChart, hflatChart, hoverlap, hcollar, hsourceCap, hsourceSeam, hcap, hseam⟩ :=
    exists_stackCapTag_transport_of_fixed_neighborhood Cp Fm Nm hNm hCpNm
      (fun y hy => (hFmfix y hy).1)
  have hLm : IsCompact Lm := by
    change IsCompact (Hinv '' (Q '' Ym))
    rw [← hFmcap]
    exact Cm.cap_isCompact.image Fm.continuous
  have hHheight (p : P) : ⟪(u : E3), Hinv p⟫_ℝ = p.1 := by
    rw [← heightPlaneCoordinates_snd]
    exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (p.2, p.1))
  have hLmheight (y : E3) (hy : y ∈ Lm) : ⟪(u : E3), y⟫_ℝ ≤ ell := by
    obtain ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩ := hy
    rw [hHheight, hQh _ (hYms ⟨q, hq, rfl⟩)]
    have hg := (stackCanonicalModel_southern_geometry rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 hprofileGap
      (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q) hq).2.2.2.1
    change (M (heightCoordinates (q : E3))).2 ≤ 0 at hg
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hlm.le hg)
  have hs1 : Cp1.cutHeight + Cp1.sign * Cp1.removal = r := by
    rw [hcut, hsign, hrem]
  have hKplus (y : E3) (hy : y ∈ K) :
      0 ≤ Cp1.sign * (⟪(u : E3), y⟫_ℝ -
        (Cp1.cutHeight + Cp1.sign * Cp1.removal)) := by
    rw [hs1, hsign, hCp, neg_one_mul]
    linarith only [(hheight y hy).2]
  have hLplus (y : E3) (hy : y ∈ Lm) :
      r - ell ≤ Cp1.sign * (⟪(u : E3), y⟫_ℝ -
        (Cp1.cutHeight + Cp1.sign * Cp1.removal)) := by
    rw [hs1, hsign, hCp, neg_one_mul]
    linarith only [hLmheight y hy]
  have hcover1 : range (fun q : UnitTwoSphere => Fm (psi (q, 0))) =
      K ∪ Cp1.cap ∪ Lm := by
    rw [hcap, hcoverm]
    exact union_right_comm K Lm Cp.cap
  have hQsp : Icc (Cp1.cutHeight + Cp1.sign * Cp1.removal - epsilon)
      (Cp1.cutHeight + Cp1.sign * Cp1.removal + epsilon) ×ˢ closedBall (0 : E2) 1 ⊆
      Q.source := by
    rw [hs1]
    intro p hp
    apply hQs
    exact ⟨⟨by linarith only [hp.1.1, hlr], hp.1.2⟩, hp.2⟩
  have hend : stackCapEndChart Cp1 Rp = stackCapEndChart Cp Rp := by
    simp only [stackCapEndChart, htube]
  have hmatch1 : ∀ z ∈ Icc (Cp1.cutHeight + Cp1.sign * Cp1.removal - epsilon)
      (Cp1.cutHeight + Cp1.sign * Cp1.removal + epsilon), ∀ x : E2,
      |‖x‖ - 1| < delta → stackCapEndChart Cp1 Rp (z, x) = Q (z, x) := by
    rw [hs1, hend]
    exact hmatchp
  obtain ⟨lp, hlp, hlpscale, hlpsmall, Fp, Np, hpsip, hNp, hLmNp, hFpfix,
      hFpK, hFpiK, hFpseam, hFptrack, hYps, hFpcap, hFpicap, hKcp, hLpLm, hcoverp⟩ :=
    exists_stackCapNormalization_in_matched_chart Cp1 hpsim K Lm hK hLm
      (r - ell) (sub_pos.mpr hlr) hcover1 (by rw [hseam]; exact hsp)
      hKplus hLplus Rp Q hQ hQi hQh epsilon delta hepsilon hdelta hQsp hmatch1
      rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hprofileGap
  let Yp := (fun q : UnitTwoSphere =>
    (r - lp * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let Lp := Hinv '' (Q '' Yp)
  have hYp : (fun q : UnitTwoSphere =>
      ((Cp1.cutHeight + Cp1.sign * Cp1.removal) +
          Cp1.sign * lp * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus = Yp := by
    dsimp only [Yp]
    rw [hs1]
    simp only [hsign, hCp, neg_mul, one_mul, sub_eq_add_neg]
  rw [hYp] at hYps hFpcap hFpicap hKcp hLpLm hcoverp
  have hFpLm : Fp '' Lm = Lm := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [(hFpfix x (hLmNp hx)).1]
    · intro hy
      exact ⟨y, hy, (hFpfix y (hLmNp hy)).1⟩
  have hFpiLm : Fp.symm '' Lm = Lm := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [(hFpfix x (hLmNp hx)).2]
    · intro hy
      exact ⟨y, hy, (hFpfix y (hLmNp hy)).2⟩
  have hFmCp : Fm '' Cp.cap = Cp.cap := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [(hFmfix x (hCpNm hx)).1]
    · intro hy
      exact ⟨y, hy, (hFmfix y (hCpNm hy)).1⟩
  let F := Fm.trans Fp
  have hFK : F '' K = K := by
    change (fun y => Fp (Fm y)) '' K = K
    rw [← image_image (fun y => Fp y) (fun y => Fm y) K, hFmK, hFpK]
  have hFiK : F.symm '' K = K := by
    change (fun y => Fm.symm (Fp.symm y)) '' K = K
    rw [← image_image (fun y => Fm.symm y) (fun y => Fp.symm y) K, hFpiK, hFmiK]
  have hFCm : F '' Cm.cap = Lm := by
    change (fun y => Fp (Fm y)) '' Cm.cap = Lm
    rw [← image_image (fun y => Fp y) (fun y => Fm y) Cm.cap, hFmcap, hFpLm]
  have hFCp : F '' Cp.cap = Lp := by
    change (fun y => Fp (Fm y)) '' Cp.cap = Lp
    rw [← image_image (fun y => Fp y) (fun y => Fm y) Cp.cap, hFmCp, ← hcap]
    exact hFpcap
  have hFiLm : F.symm '' Lm = Cm.cap := by
    rw [← hFCm, image_image]
    simp only [F.symm_apply_apply, image_id']
  have hFiLp : F.symm '' Lp = Cp.cap := by
    rw [← hFCp, image_image]
    simp only [F.symm_apply_apply, image_id']
  have hseamcap (C : SurgeryCapTag psi u) : C.seam ⊆ C.cap := by
    rw [C.seam_eq_image, C.cap_eq_image]
    exact image_mono (fun _ hy => hy.le)
  have hFseam (y : E3) (hy : y ∈ Cm.seam ∪ Cp.seam) : F y = y ∧ F.symm y = y := by
    rcases hy with hy | hy
    · have hyLm : y ∈ Lm := by rw [← hKcm] at hy; exact hy.2
      have hm := hFmseam y hy
      have hp := hFpfix y (hLmNp hyLm)
      constructor
      · change Fp (Fm y) = y
        rw [hm.1, hp.1]
      · change Fm.symm (Fp.symm y) = y
        rw [hp.2, hm.2]
    · have hm := hFmfix y (hCpNm (hseamcap Cp hy))
      have hp := hFpseam y (hseam.symm ▸ hy)
      constructor
      · change Fp (Fm y) = y
        rw [hm.1, hp.1]
      · change Fm.symm (Fp.symm y) = y
        rw [hp.2, hm.2]
  have htrackm (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      F (Cm.profile.capMap Cm.tube Cm.cutHeight Cm.sign Cm.removal Cm.scale q) =
        stackCapCanonicalEndpoint Cm rFlat rOne v0 v1 lm q := by
    have hcq : Cm.profile.capMap Cm.tube Cm.cutHeight Cm.sign Cm.removal Cm.scale q ∈
        Cm.cap := Cm.cap_eq_image.symm ▸ ⟨q, hq, rfl⟩
    have himage := hFmcap ▸ mem_image_of_mem Fm hcq
    change Fp (Fm _) = _
    rw [(hFpfix _ (hLmNp himage)).1]
    exact hFmtrack q hq
  have htrackp (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      F (Cp.profile.capMap Cp.tube Cp.cutHeight Cp.sign Cp.removal Cp.scale q) =
        stackCapCanonicalEndpoint Cp rFlat rOne v0 v1 lp q := by
    have hcq : Cp.profile.capMap Cp.tube Cp.cutHeight Cp.sign Cp.removal Cp.scale q ∈
        Cp.cap := Cp.cap_eq_image.symm ▸ ⟨q, hq, rfl⟩
    change Fp (Fm _) = _
    rw [(hFmfix _ (hCpNm hcq)).1]
    have hh := hFptrack q hq
    simpa only [hprofile, htube, hcut, hsign, hrem, hscale,
      stackCapCanonicalEndpoint] using hh
  refine ⟨lm, lp, hlm, hlmscale, hlmsmall, hlp, hscale ▸ hlpscale, hlpsmall,
    Fm, Cp1, Fp, Nm, Np, hprofile, htube, hcut, hrem, hsign, hscale, hbeta,
    hsourceChart, hflatChart, hoverlap, hcollar, hsourceCap, hsourceSeam, hcap, hseam,
    hpsim, hpsip, hNm, hCpNm, hFmfix, hNp, hLmNp, hFpfix, hFmK, hFmiK,
    hFpK, hFpiK, hFK, hFiK, hYms, hYps, hFmcap, hFpLm, hFpiLm, hFCm, hFCp,
    hFiLm, hFiLp, hFseam, hFmtrack, hFptrack, htrackm, htrackp, hKcm,
    hKcp.trans hseam, hLpLm.symm, ?_⟩
  exact hcoverp.trans (union_right_comm K Lp Lm)

end PoincareConjecture.M25.Topology3D
