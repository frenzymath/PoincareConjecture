import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreMiddleGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.CompactCapComplement

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.morse_rest_flow_segment
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : 2 * rho ^ 2 < D)
    (hsource : closedBall (0 : E2) rho ⊆ F.source)
    (c kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ x ∈ closedBall (0 : E2) rho,
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal + 3 * D < c)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (V : E3 → E3) (L M : ℝ≥0)
    (hL : LipschitzWith L V) (hM : ∀ y : E3, ‖V y‖ ≤ M)
    (U : Set E3) (hU : IsOpen U)
    (hrestU : S.retainedCore i \
      ((fun q : UnitTwoSphere => psi i (q, 0)) '' (F '' ball (0 : E2) rho)) ⊆ U)
    (hunit : ∀ y ∈ U, ⟪(u : E3), V y⟫_ℝ = 1)
    (hsphere : ∀ y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)),
      ∀ t : ℝ, boundedFlow V hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0))) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let z0 : ℝ := c + 2 * kappa * rho ^ 2
    ∀ y ∈ rest,
      ∀ t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ),
        boundedFlow V hL hM y t ∈ rest ∧
        ⟪(u : E3), boundedFlow V hL hM y t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t := by
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let disc : Set E3 := j '' (F '' closedBall (0 : E2) rho)
  let discOpen : Set E3 := j '' (F '' ball (0 : E2) rho)
  let seam : Set E3 := j '' (F '' sphere (0 : E2) rho)
  let rest : Set E3 := S.retainedCore i \ discOpen
  let s : ℝ := c + kappa * rho ^ 2
  let z0 : ℝ := c + 2 * kappa * rho ^ 2
  change ∀ y ∈ rest, ∀ t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ),
    boundedFlow V hL hM y t ∈ rest ∧
    ⟪(u : E3), boundedFlow V hL hM y t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t
  obtain ⟨hdisc, _hseam, _hseamConn, hdiff, _hzsmall, hzside, hl, hu, hfull, _hmiss⟩ :=
    S.morse_disc_middle_geometry i F rho hrho hsmall hsource c kappa hkappa
      hform hlower hupper
  change IsCompact disc at hdisc
  change disc \ discOpen = seam at hdiff
  change 0 < kappa * (z0 - s) at hzside
  have hopen := (nativeDiscChart_geometry F rho hrho hsource).2.2.2.1
  have hj : Continuous j := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hjinj : Function.Injective j := by
    intro q q' hqq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hqq)
  have hrestImage : j '' (S.sourceCore i \ F '' ball (0 : E2) rho) = rest := by
    rw [image_sdiff hjinj]
    rfl
  have hrestCompact : IsCompact rest := hrestImage ▸
    ((S.sourceCore_compact_connected i).1.diff hopen).image hj
  have hopenDisc : discOpen ⊆ disc := image_mono (image_mono ball_subset_closedBall)
  have hpath (gamma : ℝ → E3) (T : ℝ)
      (hT : T ∈ uIcc 0 (z0 - ⟪(u : E3), gamma 0⟫_ℝ))
      (hcont : ContinuousOn gamma (uIcc 0 T))
      (hgs : ∀ t ∈ uIcc 0 T, gamma t ∈ range j)
      (hstart : gamma 0 ∈ rest)
      (hheight : ∀ t ∈ uIcc 0 T,
        ⟪(u : E3), gamma t⟫_ℝ = ⟪(u : E3), gamma 0⟫_ℝ + t) :
      ∀ t ∈ uIcc 0 T, gamma t ∈ rest := by
    have hcore := S.retainedCore_of_affine_height_path i z0 hl hu gamma T hT
      hcont hgs hstart.1 hheight
    intro t ht
    by_cases ht0 : t = 0
    · simpa only [ht0] using hstart
    by_contra hout
    have hO : gamma t ∈ discOpen := by
      by_contra hnot
      exact hout ⟨hcore t ht, hnot⟩
    have hA : gamma t ∈ disc := hopenDisc hO
    have hnotseam : gamma t ∉ seam := by
      intro h
      have hd : gamma t ∈ disc \ discOpen := by rw [hdiff]; exact h
      exact hd.2 hO
    have hstrict := (hfull (gamma t) hA).2.2.2.2.mpr hnotseam
    change kappa * (⟪(u : E3), gamma t⟫_ℝ - s) < 0 at hstrict
    have hsub : uIcc 0 t ⊆ uIcc 0 T := uIcc_subset_uIcc_left ht
    have himage : gamma '' uIcc 0 t ⊆ disc ∪ rest := by
      rintro y ⟨v, hv, rfl⟩
      by_cases hvO : gamma v ∈ discOpen
      · exact Or.inl (hopenDisc hvO)
      · exact Or.inr ⟨hcore v (hsub hv), hvO⟩
    have hpre : IsPreconnected (gamma '' uIcc 0 t) :=
      isPreconnected_uIcc.image gamma (hcont.mono hsub)
    obtain ⟨y, ⟨w, hw, rfl⟩, hwA, hwR⟩ := isPreconnected_closed_iff.mp hpre
      disc rest hdisc.isClosed hrestCompact.isClosed himage
        ⟨gamma t, ⟨t, right_mem_uIcc, rfl⟩, hA⟩
        ⟨gamma 0, ⟨0, left_mem_uIcc, rfl⟩, hstart⟩
    have hwseam : gamma w ∈ seam := by
      rw [← hdiff]
      exact ⟨hwA, hwR.2⟩
    have hwheight : ⟪(u : E3), gamma w⟫_ℝ = s :=
      (hfull (gamma w) hwA).2.2.2.1.mpr hwseam
    have hsign : kappa = 1 ∨ kappa = -1 := by
      apply abs_eq_abs.mp
      simpa only [abs_one] using hkappa
    have hht := hheight t ht
    have hhw := hheight w (hsub hw)
    have htarget : t ∈ uIcc 0 (z0 - ⟪(u : E3), gamma 0⟫_ℝ) :=
      uIcc_subset_uIcc_left hT ht
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · have htw : t ≤ w := by
        rw [uIcc_of_ge hneg.le] at hw
        exact hw.1
      have hz : z0 ≤ ⟪(u : E3), gamma t⟫_ℝ := by
        rcases mem_uIcc.mp htarget with h | h <;> linarith only [h.1, h.2, hneg, hht]
      rcases hsign with hs | hs
      · rw [hs, one_mul] at hstrict hzside
        linarith only [hstrict, hzside, hz]
      · rw [hs, neg_one_mul] at hstrict
        linarith only [hstrict, hwheight, hht, hhw, htw]
    · have hwt : w ≤ t := by
        rw [uIcc_of_le hpos.le] at hw
        exact hw.2
      have hz : ⟪(u : E3), gamma t⟫_ℝ ≤ z0 := by
        rcases mem_uIcc.mp htarget with h | h <;> linarith only [h.1, h.2, hpos, hht]
      rcases hsign with hs | hs
      · rw [hs, one_mul] at hstrict
        linarith only [hstrict, hwheight, hht, hhw, hwt]
      · rw [hs, neg_one_mul] at hstrict hzside
        linarith only [hstrict, hzside, hz]
  intro y hy
  let gamma : ℝ → E3 := boundedFlow V hL hM y
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  have hg0 : gamma 0 = y := boundedFlow_zero V hL hM y
  have hgc : Continuous gamma := continuous_iff_continuousAt.mpr
    (fun t => (boundedFlow_hasDerivAt V hL hM y t).continuousAt)
  have hh : Continuous (fun t => ⟪(u : E3), gamma t⟫_ℝ) :=
    continuous_const.inner hgc
  have hprefix (v : ℝ) (hv : MapsTo gamma (uIcc 0 v) U) :
      ∀ t ∈ uIcc 0 v, ⟪(u : E3), gamma t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t := by
    intro t ht
    have hd (w : ℝ) (hw : w ∈ uIcc 0 t) :
        HasDerivAt (fun z => ⟪(u : E3), gamma z⟫_ℝ) 1 w := by
      have hder := H.hasFDerivAt.comp_hasDerivAt w
        (boundedFlow_hasDerivAt V hL hM y w)
      change HasDerivAt (fun z => ⟪(u : E3), gamma z⟫_ℝ)
        ⟪(u : E3), V (gamma w)⟫_ℝ w at hder
      rw [hunit _ (hv (uIcc_subset_uIcc_left ht hw))] at hder
      exact hder
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · obtain ⟨w, _hw, he⟩ := exists_hasDerivAt_eq_slope
        (fun z => ⟪(u : E3), gamma z⟫_ℝ) (fun _ => (1 : ℝ)) hneg
        hh.continuousOn (fun w hw => hd w (by
          rw [uIcc_of_ge hneg.le]
          exact ⟨hw.1.le, hw.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hneg.ne')).mp he
      rw [hg0] at he'
      linarith only [he']
    · simp only [heq, hg0, add_zero]
    · obtain ⟨w, _hw, he⟩ := exists_hasDerivAt_eq_slope
        (fun z => ⟪(u : E3), gamma z⟫_ℝ) (fun _ => (1 : ℝ)) hpos
        hh.continuousOn (fun w hw => hd w (by
          rw [uIcc_of_le hpos.le]
          exact ⟨hw.1.le, hw.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hpos.ne')).mp he
      rw [hg0] at he'
      linarith only [he']
  have hys : y ∈ range j := by
    obtain ⟨q, _hq, rfl⟩ := hy.1
    exact ⟨q, rfl⟩
  have hgs (t : ℝ) : gamma t ∈ range j := hsphere y hys t
  have hstart : gamma 0 ∈ rest := hg0.symm ▸ hy
  have hwhole : MapsTo gamma (uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ)) U := by
    apply hgc.continuousOn.mapsTo_uIcc_of_closed_prefix_trap hU
      hrestCompact.isClosed (hrestU hstart) (fun _ h => hrestU h.1)
    intro v hv hvg
    apply hpath gamma v (by simpa only [hg0] using hv) hgc.continuousOn
      (fun t _ => hgs t) hstart _ v right_mem_uIcc
    intro t ht
    simpa only [hg0] using hprefix v hvg t ht
  have hheight := hprefix (z0 - ⟪(u : E3), y⟫_ℝ) hwhole
  have hrest := hpath gamma (z0 - ⟪(u : E3), y⟫_ℝ)
    (by simpa only [hg0] using
      (right_mem_uIcc : z0 - ⟪(u : E3), y⟫_ℝ ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ)))
    hgc.continuousOn (fun t _ => hgs t) hstart
    (fun t ht => by simpa only [hg0] using hheight t ht)
  exact fun t ht => ⟨hrest t ht, hheight t ht⟩

theorem FamilyCutState.morse_rest_middle_retraction
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : 2 * rho ^ 2 < D)
    (hsource : closedBall (0 : E2) rho ⊆ F.source)
    (hdisc : F '' closedBall (0 : E2) rho ⊆ S.sourceCore i)
    (c kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ x ∈ closedBall (0 : E2) rho,
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal + 3 * D < c)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (V : E3 → E3) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (L M : ℝ≥0) (hL : LipschitzWith L V) (hM : ∀ y : E3, ‖V y‖ ≤ M)
    (U : Set E3) (hU : IsOpen U)
    (hrestU : S.retainedCore i \
      ((fun q : UnitTwoSphere => psi i (q, 0)) '' (F '' ball (0 : E2) rho)) ⊆ U)
    (hunit : ∀ y ∈ U, ⟪(u : E3), V y⟫_ℝ = 1)
    (hsphere : ∀ y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)),
      ∀ t : ℝ, boundedFlow V hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0))) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let z0 : ℝ := c + 2 * kappa * rho ^ 2
    let R : E3 → E3 := fun y =>
      boundedFlow V hL hM y (z0 - ⟪(u : E3), y⟫_ℝ)
    Continuous R ∧
      R '' rest = collarHeightLevel (psi i) (u : E3) z0 ∧
      (∀ y ∈ collarHeightLevel (psi i) (u : E3) z0, R y = y) ∧
      IsCompact (collarHeightLevel (psi i) (u : E3) z0) ∧
      IsConnected (collarHeightLevel (psi i) (u : E3) z0) := by
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let z0 : ℝ := c + 2 * kappa * rho ^ 2
  let R : E3 → E3 := fun y => boundedFlow V hL hM y (z0 - ⟪(u : E3), y⟫_ℝ)
  have hj : Continuous j := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hjinj : Function.Injective j := by
    intro q q' hqq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hqq)
  obtain ⟨_hzero, hopenDisc, _htarget, hopen, hDcompact, _hseam,
    hseamConn, _hclosure, hdiff, _hfrontier⟩ := nativeDiscChart_geometry F rho hrho hsource
  obtain ⟨hKcompact, hKconn⟩ := S.sourceCore_compact_connected i
  have hboundaryConn : IsConnected
      ((F '' closedBall (0 : E2) rho) \ F '' ball (0 : E2) rho) := by
    rw [hdiff]
    exact hseamConn
  obtain ⟨_hrestCompact, hrestConn, _hintersection⟩ :=
    compact_connected_diff_of_connected_seam hKcompact hKconn hDcompact hdisc
      hopen hopenDisc hboundaryConn
  have hrestImage : j '' (S.sourceCore i \ F '' ball (0 : E2) rho) = rest := by
    rw [image_sdiff hjinj]
    rfl
  have hconn : IsConnected rest := hrestImage ▸ hrestConn.image j hj.continuousOn
  obtain ⟨_hdiscC, _hseamC, _hseamN, _hdiff, _hzsmall, _hzside,
    hl, hu, _hfull, hmiss⟩ := S.morse_disc_middle_geometry i F rho hrho hsmall
      hsource c kappa hkappa hform hlower hupper
  have hR : Continuous R := (boundedFlow_contDiff V hL hM hV hVc).continuous.comp
    (continuous_id.prodMk (continuous_const.sub (continuous_const.inner continuous_id)))
  obtain ⟨_hK, _hKconn, _hdef, hcover, _hinter⟩ := S.retainedCore_geometry i
  have hlevelRest : collarHeightLevel (psi i) (u : E3) z0 ⊆ rest := by
    rintro y ⟨q, hq, rfl⟩
    have hh : ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0 := hq
    have hcore : psi i (q, 0) ∈ S.retainedCore i := by
      have hy : psi i (q, 0) ∈ range j := ⟨q, rfl⟩
      rw [hcover] at hy
      rcases hy with hcore | hcaps
      · exact hcore
      · obtain ⟨a, ha⟩ := mem_iUnion.mp hcaps
        have hside := ((S.cap a.1).cap_seam_signed_height _ ha).1
        have hsign : (S.cap a.1).sign = 1 ∨ (S.cap a.1).sign = -1 := by
          apply abs_eq_abs.mp
          simpa only [abs_one] using (S.cap a.1).sign_abs
        rcases hsign with hs | hs
        · have hlow := hl a.1 a.2 hs
          simp only [hs, one_mul] at hside hlow
          exfalso
          linarith only [hside, hlow, hh]
        · have hupp := hu a.1 a.2 hs
          simp only [hs, neg_one_mul] at hside hupp
          exfalso
          linarith only [hside, hupp, hh]
    refine ⟨hcore, ?_⟩
    intro hopenMem
    have hdiscMem : psi i (q, 0) ∈ j '' (F '' closedBall (0 : E2) rho) :=
      image_mono (image_mono ball_subset_closedBall) hopenMem
    exact hmiss _ hdiscMem hh
  have hfix : ∀ y ∈ collarHeightLevel (psi i) (u : E3) z0, R y = y := by
    rintro y ⟨q, hq, rfl⟩
    change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0 at hq
    dsimp only [R]
    rw [hq, sub_self, boundedFlow_zero]
  have himage : R '' rest = collarHeightLevel (psi i) (u : E3) z0 := by
    apply subset_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyRest, hh⟩ := S.morse_rest_flow_segment i F rho hrho hsmall hsource
        c kappa hkappa hform hlower hupper V L M hL hM U hU hrestU hunit hsphere
        y hy (z0 - ⟪(u : E3), y⟫_ℝ) right_mem_uIcc
      obtain ⟨q, _hq, heq⟩ := hyRest.1
      change psi i (q, 0) = R y at heq
      refine ⟨q, ?_, heq⟩
      change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0
      rw [heq]
      change ⟪(u : E3), R y⟫_ℝ = ⟪(u : E3), y⟫_ℝ +
        (z0 - ⟪(u : E3), y⟫_ℝ) at hh
      linarith only [hh]
    · intro y hy
      exact ⟨y, hlevelRest hy, hfix y hy⟩
  exact ⟨hR, himage, hfix, collarHeightLevel_compact (psi i) (S.embedding i) (u : E3) z0,
    himage ▸ hconn.image R hR.continuousOn⟩

end PoincareConjecture.M25.Topology3D
