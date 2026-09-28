import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RawPieceBandInput
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallGerms
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedLowerExteriorArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallCircleFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedOrientedExteriorArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedEndpointCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedConnectorImage
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedCircleImages
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedReparametrizedArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedMiddleNative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MiddleExteriorCoordinates










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix NNReal

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞



theorem exists_saddle_nested_target_middle_inputs
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (beta : ℝ) (hbeta : 0 < beta)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let L := heightPlaneCoordinates u
    ∃ (rho delta : ℝ) (hrho : 0 < rho) (hdelta : 0 < delta)
      (hsmall : delta ≤ rho ^ 2 / 128)
      (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
      (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
      (kappa : OpenPartialHomeomorph E2 E2)
      (Tlower : D2) (C : ℝ → Fin 2 → UnitCircle → E2)
      (label : Equiv.Perm (Fin 2)) (nu : ℝ)
      (alpha : Fin 2 → ℝ → E2) (X : E3 → E3)
      (T : ℝ → ℝ → D3),
      let mu : ℝ := delta / rho ^ 2
      let hmu : 0 < mu := div_pos hdelta (sq_pos_of_pos hrho)
      let hmuSmall : mu ≤ 1 / 128 :=
        (div_le_iff₀ (sq_pos_of_pos hrho)).2 (by nlinarith only [hsmall])
      let F := Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
      let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
      let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
      let port : Fin 4 → E2 := fun k =>
        J2.symm (sx k / Real.sqrt 2, sy k / Real.sqrt 2)
      let sign : Fin 2 → ℝ := ![1, -1]
      let Z : Fin 2 → Set E2 := fun k =>
        {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign k * Real.sqrt ((J2 x).1 ^ 2 + mu)}
      4 * delta < rho ^ 2 * beta ∧ W.level < c - delta ∧
      closedBall (0 : E2) 2 ⊆ kappa.source ∧
      ContDiffOn ℝ ∞ kappa kappa.source ∧
      ContDiffOn ℝ ∞ kappa.symm kappa.target ∧
      (∀ k : Fin 2, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C p.1 k p.2)) ∧
      (∀ (s : ℝ) (k : Fin 2), IsPlanarEmbedding (C s k)) ∧
      (∀ (s : ℝ) (i k : Fin 2), i ≠ k →
        Disjoint (range (C s i)) (range (C s k))) ∧
      (∀ (k : Fin 2) (q : UnitCircle), C 0 k q =
        Tlower ((L (psi (W.leg k (q, W.level), 0))).1)) ∧
      0 < nu ∧ nu < 1 / 16 ∧
      (∀ k : Fin 2, ContDiff ℝ ∞ (alpha k) ∧
        (∀ t : ℝ, deriv (alpha k) t ≠ 0) ∧
        InjOn (alpha k) (Icc (-nu) (1 + nu))) ∧
      (∀ i k : Fin 2, i ≠ k →
        Disjoint (alpha i '' Icc (-nu) (1 + nu))
          (alpha k '' Icc (-nu) (1 + nu))) ∧
      (∀ k t, t ∈ Ioo (0 : ℝ) 1 →
        alpha k t ∉ kappa '' closedBall (0 : E2) 1) ∧
      (∀ k t, t ∈ Icc (-nu) nu →
        alpha k t = kappa ((1 + t) • port (finProdFinEquiv (k, (0 : Fin 2))))) ∧
      (∀ k t, t ∈ Icc (1 - nu) (1 + nu) →
        alpha k t = kappa ((2 - t) • port (finProdFinEquiv (k, (1 : Fin 2))))) ∧
      (∀ k : Fin 2, range (C 1 (label k)) =
        (alpha k '' Icc (0 : ℝ) 1) ∪ (kappa '' ((F 1) '' Z k))) ∧
      (⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1) =
        {x : E2 | L.symm (x, c) ∈ range j} \ (kappa '' ball (0 : E2) 1) ∧
      ContDiff ℝ ∞ X ∧
      (∀ (s : ℝ) (y : E3), T s s y = y) ∧
      (∀ (s t : ℝ) (y : E3),
        HasDerivAt (fun a : ℝ => T s a y) (X (T s t y)) t) ∧
      ∀ (g : D2), EqOn g kappa (closedBall (0 : E2) 2) →
        let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
          (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
            sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
        let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r => L.symm (g (xi k t r), c + t)
        let E : ℝ → Set E2 := fun t =>
          {x : E2 | L.symm (g x, c + t) ∈ range j ∧ 1 ≤ ‖x‖}
        let Ext : ℝ → Set E3 := fun t => L.symm '' ((g '' E t) ×ˢ ({c + t} : Set ℝ))
        (∀ t : ℝ, |t| < 2 * delta → ∀ x : E2, ‖x‖ < 2 →
          (L.symm (g x, c + t) ∈ range j ↔
            t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))) ∧
        (∀ (k : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
          ∀ t : ℝ, |t| < 2 * delta →
            HasDerivAt (fun s : ℝ => Xi k s r) (X (Xi k t r)) t) ∧
        ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
          (T s t) '' Ext s = Ext t ∧ (T s t).symm '' Ext t = Ext s := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let L := heightPlaneCoordinates u
  obtain ⟨R, b, P, Araw, hR, hb, hPsource, hAsource, hPs, hPi, hAs, hAi,
    hPmorse, hPform, hPcenter, hAcenter, hAtarget, hAform, hAinverse,
    hRawDisc, hRawCylinder, hRawInverse, hCapGap, hCore, hRegular⟩ :=
    exists_raw_saddle_piece_band_input psi hpsi u D
  change P.source = {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} at hPsource
  let J2 : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let rho := 5 * R / 8
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  let epsilon := min (b / 8) (rho ^ 2 * beta)
  have hepsilon : 0 < epsilon :=
    lt_min (by positivity) (mul_pos (sq_pos_of_pos hrho) hbeta)
  let delta := min (epsilon / 8) (min ((c - W.level) / 4) (rho ^ 2 / 128))
  have hJ2 (x : E2) : (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2 := by
    change x 0 ^ 2 + x 1 ^ 2 = ‖x‖ ^ 2
    simpa only [Fin.sum_univ_two] using (EuclideanSpace.real_norm_sq_eq x).symm
  have hAgraph : ∀ w ∈ Araw.source,
      Araw w = L.symm (P w.1, w.2) ∧
      (Araw w ∈ range j ↔ w.2 = c +
        D.morseSign1 * w.1.1 ^ 2 + D.morseSign2 * w.1.2 ^ 2) := by
    intro w hw
    refine ⟨(hAform w hw).1, ?_⟩
    simpa only [j, H, c, add_assoc] using (hAform w hw).2.2

  obtain ⟨N, Bwall, Eport, hdelta, hdeltaB, hWindow, hLowerCut, hdeltaSq,
    hInnerRadius, hOuterRadius, hNid, hNswap, hN, hWallSource, hWallTarget,
    hWallForm, hWallInverse, hWallBuffer, hWallInside, hWallClosed, hWallSphere,
    hPortNorm, hPortInj, hEport, hEportDisjoint, hEportCover, hAnnularCover,
    hWallLevel, hWallLevelInj, hCriticalGraph⟩ :=
    exists_saddle_selected_wall_germs psi hpsi u D W R b epsilon hR hb
      hepsilon (min_le_left _ _) P Araw hPsource hPs hPi hPmorse hPform hAsource hAgraph
  have hSmall : delta ≤ (5 * R / 8) ^ 2 / 128 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hCoreBand (q : UnitTwoSphere) (hq : |H (j q) - c| ≤ 3 * delta) :
      q ∈ D.sourceCore := by
    apply hCore q
    have hd : 2 * delta < b / 8 := hdeltaB.trans_le (min_le_left _ _)
    linarith
  have hMorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target := by
    rw [← hPsource]
    exact hPmorse
  obtain ⟨hLowerRegular, hOldCircles, dLower, Tlower, q, label, angle, speed,
    ends, eta, hdLower, hLowerWindow, hTlower, hTlowerInv, hTlowerZero,
    hTlowerSupport, hLowerCircles, hLowerDisjoint, hLowerMembership,
    hLowerCover, hLowerCases, hq, hqDisjoint, hqLevel, hqReconstruction,
    hNativePorts, heta, hetaSmall, hRemovedParents, hSourceArcs,
    hSourceArcsDisjoint, hExteriorCover, hSourceRim, hEndpointPairs⟩ :=
    exists_saddle_selected_lower_exterior_arcs psi hpsi u D W R delta hR hdelta
      hSmall hLowerCut.le hMorse hCoreBand N hN
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let sourcePort : Fin 4 → UnitTwoSphere := fun k => D.morse.symm
    (N (sx k * Real.sqrt ((rho ^ 2 - delta) / 2),
      sy k * Real.sqrt ((rho ^ 2 + delta) / 2)))
  let Dc : Set UnitTwoSphere := D.morse.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
  let V : Set UnitTwoSphere := D.morse.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
  let La : Set UnitTwoSphere := {p | H (j p) = c - delta}
  obtain ⟨angleNew, speedNew, hAngleNew, hSpeedNew, hArcReflection,
    hArcImages, hOrderedArcs, hOrderedDisjoint, hOrderedCover⟩ :=
    exists_saddle_selected_oriented_exterior_arcs q label angle speed ends eta
      sourcePort Dc V La hSourceArcs hSourceArcsDisjoint hExteriorCover hEndpointPairs
  have hmu : 0 < delta / rho ^ 2 := div_pos hdelta (sq_pos_of_pos hrho)
  have hmuSmall : delta / rho ^ 2 ≤ 1 / 128 := by
    apply (div_le_iff₀ (sq_pos_of_pos hrho)).2
    have hbound : delta ≤ rho ^ 2 / 128 := hSmall
    linarith only [hbound]

  obtain ⟨ks, hksSource, hksTarget, hksForm, hksInverse, hksBuffer,
    hks, hksInv, hCoordinates, hNoSheets⟩ :=
    exists_saddle_selected_source_chart psi hpsi u D R b delta hR hWindow
      P Araw hPsource hPmorse (fun s hs => (hPform s hs).2)
      hAsource hAgraph J2 hJ2 N (fun s => (hN s).2) Bwall.chart hWallForm
  obtain ⟨hOpenDisc, hClosedDisc, hBranch⟩ :=
    saddle_selected_source_geometry psi u D rho hrho J2 hJ2 N
      (fun s => (hN s).2.1) ks hksForm
  obtain ⟨Xfield, Klip, Lbound, hKlip, hLbound, hXfield, hcXfield,
    Csupport, hCarrierCompact, hFieldSupport, hCarrier, hPhi, hPhiInv,
    hFlow, hPhiSupport, hPhiSphere, hPhiFix, hFieldHeight,
    hDoOpen, hDcCompact, hDoClosure, hNativePoints, hNativeRim,
    hNative, hPhiExterior⟩ :=
    exists_saddle_selected_wall_transport psi hpsi u D R delta hR hdelta
      hSmall hMorse hCoreBand N hN
  let Phi : ℝ → D3 := fun t =>
    boundedFlowDiffeomorph Xfield hKlip hLbound hXfield hcXfield t
  have hPhiZero (y : E3) : Phi 0 y = y :=
    boundedFlow_zero Xfield hKlip hLbound y
  let Xbranch : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
    (sx i * Real.sqrt ((r ^ 2 + a) / 2), sy i * Real.sqrt ((r ^ 2 - a) / 2))
  let Es : ℝ → Set E3 := fun z =>
    (range j ∩ {y | H y = c + z}) \ (j '' (ks '' ball (0 : E2) 1))
  let Elevel : ℝ → Set E3 := fun z =>
    (range j ∩ {y | H y = c + z}) \ (j '' V)
  change ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
    Phi (t - s) '' Elevel s = Elevel t ∧
    (Phi (t - s)).symm '' Elevel t = Elevel s at hPhiExterior
  have hEs (z : ℝ) : Es z = Elevel z := by
    dsimp only [Es, Elevel]
    rw [hOpenDisc]
  have hLower : |(-delta : ℝ)| ≤ 2 * delta := by
    rw [abs_neg, abs_of_pos hdelta]
    linarith
  have hTrackHeight (tau : ℝ) (htau : tau ∈ Icc (0 : ℝ) delta) :
      |-delta + tau| ≤ 2 * delta :=
    abs_le.mpr ⟨by linarith [htau.1], by linarith [htau.2]⟩
  have hExteriorA2 : ∀ tau ∈ Icc (0 : ℝ) delta,
      Phi tau '' Es (-delta) = Es (-delta + tau) := by
    intro tau htau
    rw [hEs, hEs]
    have htime : -delta + tau - -delta = tau := by ring
    simpa only [htime] using
      (hPhiExterior (-delta) (-delta + tau) hLower (hTrackHeight tau htau)).1
  have hNativeA2 : ∀ tau ∈ Icc (0 : ℝ) delta, ∀ i : Fin 4,
      ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
        Phi tau (j (ks (Xbranch (-delta / rho ^ 2) (1 + a) i))) =
          j (ks (Xbranch ((-delta + tau) / rho ^ 2) (1 + a) i)) := by
    intro tau htau i a ha
    change Phi tau (j (ks (J2.symm _))) = j (ks (J2.symm _))
    rw [hBranch (-delta) (1 + a) i, hBranch (-delta + tau) (1 + a) i]
    have htime : -delta + tau - -delta = tau := by ring
    simpa only [htime] using
      hNative i a (abs_lt.mpr ha) (-delta) (-delta + tau)
        hLower (hTrackHeight tau htau)
  let timeCut : ℝ → ℝ := Real.smoothTransition
  let mu := delta / rho ^ 2
  let Fangular := Classical.choose (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  obtain ⟨hFangular, hFangularInv, hFangularForm, hFNorm, hFZero, hFOne,
    hFC, hFSupport, hFX, hFSigns⟩ :=
    Classical.choose_spec (exists_saddle_angular_reconnection
      J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  change ∀ t i r, r ∈ Icc (3 / 4 : ℝ) (5 / 4) →
    Fangular t (Xbranch (-mu) r i) =
      Xbranch (-(1 - timeCut t) * mu) r i at hFX
  have hAngular : ∀ t : ℝ, ∀ i : Fin 4,
      ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
        Fangular t (Xbranch (-delta / rho ^ 2) (1 + a) i) =
          Xbranch ((-delta + timeCut t * delta) / rho ^ 2) (1 + a) i := by
    intro t i a ha
    have hstart : -delta / rho ^ 2 = -mu := by dsimp [mu]; ring
    have hend : (-delta + timeCut t * delta) / rho ^ 2 =
        -(1 - timeCut t) * mu := by dsimp [mu]; ring
    rw [hstart, hend]
    exact hFX t i (1 + a) ⟨by linarith [ha.1], by linarith [ha.2]⟩
  let Alevel : ℝ → UnitTwoSphere → E2 := fun t p =>
    if p ∈ ks '' ball (0 : E2) 1 then Bwall.chart (Fangular t (ks.symm p))
    else horizontalBandProjection u (Phi (timeCut t * delta) (j p))
  obtain ⟨hGInjective, hGRegions, hOverlap, hGExterior, hGInterior⟩ :=
    saddle_selected_level_gluing psi hpsi u c rho delta hrho hdelta
      hSmall J2 hJ2 ks Bwall.chart hksBuffer hWallBuffer Phi Fangular
      (fun t x => (hFNorm t x).1)
      hCoordinates hNoSheets hExteriorA2 hNativeA2 hAngular
  obtain ⟨C, hC, hCEmbedding, hCDisjoint, hCStart, hCEnd, hCInside,
    hCOutside, hCExterior, hCInterior, hCBypass⟩ :=
    exists_saddle_selected_closed_circle_family psi hpsi u c rho delta hrho hdelta
      hSmall J2 hJ2 ks Bwall.chart hksBuffer hWallBuffer hks hksInv
      Bwall.smooth Bwall.smooth_symm 2 q hq hqDisjoint
      Phi hPhi hPhiZero Fangular hFangular (fun t x => (hFNorm t x).1)
      (fun t x ht => (hFZero t x ht).1) (fun t x ht => (hFOne t x ht).1)
      hCoordinates hNoSheets hqLevel hExteriorA2 hNativeA2 hAngular
  have hCglue (t : ℝ) (i : Fin 2) (theta : UnitCircle) :
      C t i theta = Alevel t (q i theta) := by
    by_cases hp : q i theta ∈ ks '' ball (0 : E2) 1
    · rw [hCInside t i theta ((image_mono ball_subset_closedBall) hp)]
      simp only [Alevel, if_pos hp]
    · rw [hCOutside t i theta hp]
      simp only [Alevel, if_neg hp, timeCut, j]
  let phase : Fin 2 → ℝ → UnitCircle := fun i t =>
    complexUnitCircleHomeomorph (Circle.exp (angleNew i + speedNew i * t))
  let src : Fin 2 → ℝ → UnitTwoSphere := fun i t => q (label i) (phase i t)
  have hEportSource (k : Fin 4) : (Eport k).source =
      Ioo (-2 * delta) (2 * delta) ×ˢ Ioo (-(1 / 8) : ℝ) (1 / 8) :=
    (hEport k).1
  have hEportFirst (k : Fin 4) (p : UnitTwoSphere) (hp : p ∈ (Eport k).target) :
      ((Eport k).symm p).1 = H (j p) - c :=
    congrArg Prod.fst ((hEport k).2.2.2.2.2.2.1 p hp)
  have hEportClosed (k : Fin 4) (w : ℝ × ℝ) (hw : w ∈ (Eport k).source) :
      Eport k w ∈ Dc ↔ w.2 ≤ 0 := by
    rcases hEport k with ⟨hsource, -, -, -, -, hform, -, -, -, -, hregions⟩
    have hwU := hw
    rw [hEportSource] at hwU
    have hheight : H (j (Eport k w)) = c + w.1 := by
      have heq := congrArg (fun y : E3 => (L y).2) (hform w hwU).2.2.1
      simpa only [L, H, j, c, InnerProductSpace.toDual_apply_apply,
        heightPlaneCoordinates_snd, ContinuousLinearEquiv.apply_symm_apply] using heq
    have habs : |w.1| ≤ 2 * delta :=
      (abs_lt.mpr ⟨by linarith [hwU.1.1], hwU.1.2⟩).le
    dsimp only [Dc]
    rw [← hClosedDisc]
    refine ((hNoSheets w.1 habs (Eport k w) hheight).2).symm.trans ?_
    exact (hregions w hwU).2.2
  have hEportZero (k : Fin 4) : Eport k (-delta, 0) = sourcePort k := by
    have hw : (-delta, (0 : ℝ)) ∈
        Ioo (-2 * delta) (2 * delta) ×ˢ Ioo (-(1 / 8) : ℝ) (1 / 8) :=
      ⟨⟨by linarith, by linarith⟩, by norm_num⟩
    have heq := ((hEport k).2.2.2.2.2.1 (-delta, 0) hw).1
    simpa only [sourcePort, sx, sy, rho, add_zero, one_pow, mul_one,
      sub_neg_eq_add, ← sub_eq_add_neg] using heq
  have hSrcLevel (i : Fin 2) (t : ℝ) : H (j (src i t)) - c = -delta := by
    have hm : src i t ∈ La := by
      have hcover : (⋃ k : Fin 2, range (q k)) = La := hqLevel
      rw [← hcover]
      exact mem_iUnion.mpr ⟨label i, mem_range_self (phase i t)⟩
    change H (j (src i t)) = c - delta at hm
    linarith only [hm]
  have hSrcEnds (i : Fin 2) :
      src i 0 = Eport (finProdFinEquiv (i, (0 : Fin 2))) (-delta, 0) ∧
      src i 1 = Eport (finProdFinEquiv (i, (1 : Fin 2))) (-delta, 0) := by
    rcases hOrderedArcs i with ⟨-, -, -, -, -, h0, h1, -, -, -, -⟩
    exact ⟨h0.trans (hEportZero _).symm, h1.trans (hEportZero _).symm⟩
  have hSrcExterior (i : Fin 2) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      src i t ∉ Dc := by
    exact fun hp => Set.disjoint_left.mp (hOrderedArcs i).2.2.2.2.2.2.2.1
      ⟨t, ht, rfl⟩ hp
  have hSrcAfter (i : Fin 2) (t : ℝ) (ht : t ∈ Ioo (1 : ℝ) (1 + eta)) :
      src i t ∈ Dc := by
    have hv : src i t ∈ V := (hOrderedArcs i).2.2.2.2.2.2.2.2.2.2 t ht
    dsimp only [V] at hv
    dsimp only [Dc]
    rcases hv with ⟨s, hs, heq⟩
    refine ⟨s, ?_, heq⟩
    change s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2
    exact le_of_lt hs
  obtain ⟨eta1, heta1, heta1Old, heta1Small, hEndpoint⟩ :=
    exists_saddle_selected_endpoint_coordinates delta eta hdelta heta
      Eport hEportSource (fun k => (hEport k).2.2.1)
      (fun k => (hEport k).2.2.2.1) (fun p => H (j p) - c)
      hEportFirst Dc hEportClosed src
      (fun i => (hOrderedArcs i).2.2.1)
      (fun i => (hOrderedArcs i).2.2.2.1)
      hSrcLevel hSrcEnds hSrcExterior hSrcAfter
  let b0 : Fin 2 → ℝ → ℝ := fun i t =>
    ((Eport (finProdFinEquiv (i, (0 : Fin 2)))).symm (src i t)).2
  let b1 : Fin 2 → ℝ → ℝ := fun i t =>
    ((Eport (finProdFinEquiv (i, (1 : Fin 2)))).symm (src i t)).2
  obtain ⟨nu, Theta, hnu, hnuSmall, hTheta⟩ :=
    exists_saddle_endpoint_reparametrizations 2 eta1 heta1 heta1Small
      b0 (fun i s => 1 - b1 i s)
      (fun i => (hEndpoint i).2.2.1)
      (fun i => contDiffOn_const.sub (hEndpoint i).2.2.2.1)
      (fun i => (hEndpoint i).2.2.2.2.1)
      (fun i => by simp only [b1, (hEndpoint i).2.2.2.2.2.1, sub_zero])
      (fun i => (hEndpoint i).2.2.2.2.2.2.1)
      (fun i => (hEndpoint i).2.2.2.2.2.2.2.1)
  let port : Fin 4 → E2 := fun k =>
    J2.symm (sx k / Real.sqrt 2, sy k / Real.sqrt 2)
  have hPortNative (k : Fin 4) (z a : ℝ)
      (hz : z ∈ Ioo (-2 * delta) (2 * delta))
      (ha : a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)) :
      Eport k (z, a) = ks (Xbranch (z / rho ^ 2) (1 + a) k) :=
    ((hEport k).2.2.2.2.2.1 (z, a) ⟨hz, ha⟩).1.trans
      (hBranch z (1 + a) k).symm
  have hCriticalPort (k : Fin 4) (a : ℝ)
      (ha : a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8))
      (i : Fin 2) (theta : UnitCircle) (hp : q i theta = Eport k (-delta, a)) :
      C 1 i theta = Bwall.chart ((1 + a) • port k) := by
    let x := Xbranch (-delta / rho ^ 2) (1 + a) k
    have hnegative : -delta / rho ^ 2 = -mu := by dsimp [mu]; ring
    have hsign : (sx k) ^ 2 = 1 ∧ (sy k) ^ 2 = 1 := by
      fin_cases k <;> norm_num [sx, sy]
    have hplus : 0 ≤ ((1 + a) ^ 2 - mu) / 2 := by
      have hbound : mu ≤ 1 / 128 := hmuSmall
      nlinarith only [ha.1, hbound, sq_nonneg (1 + a - 7 / 8)]
    have hminus : 0 ≤ ((1 + a) ^ 2 + mu) / 2 :=
      div_nonneg (add_nonneg (sq_nonneg _) hmu.le) (by norm_num)
    have hnorm : ‖x‖ = 1 + a := by
      have hsquare : ‖x‖ ^ 2 = (1 + a) ^ 2 := by
        rw [← hJ2 x]
        simp only [x, Xbranch, ContinuousLinearEquiv.apply_symm_apply,
          hnegative, ← sub_eq_add_neg, sub_neg_eq_add, mul_pow,
          hsign.1, hsign.2, one_mul, Real.sq_sqrt hplus, Real.sq_sqrt hminus]
        ring
      nlinarith only [hsquare, norm_nonneg x, ha.1]
    have hx : x ∈ closedBall (0 : E2) 2 :=
      mem_closedBall_zero_iff.mpr (by rw [hnorm]; linarith only [ha.2])
    have hxs := hksBuffer hx
    have hpoint : q i theta = ks x := hp.trans
      (hPortNative k (-delta) a ⟨by linarith only [hdelta], by linarith only [hdelta]⟩ ha)
    have hinverse : ks.symm (q i theta) = x := by rw [hpoint, ks.left_inv hxs]
    have htarget : q i theta ∈ ks.target := by rw [hpoint]; exact ks.map_source hxs
    have hlevel : q i theta ∈ La := by
      have hcover : (⋃ k : Fin 2, range (q k)) = La := hqLevel
      rw [← hcover]
      exact mem_iUnion.mpr ⟨i, mem_range_self theta⟩
    have hsame : C 1 i theta = Bwall.chart (Fangular 1 x) := by
      by_cases hinside : q i theta ∈ ks '' ball (0 : E2) 1
      · rw [hCInside 1 i theta ((image_mono ball_subset_closedBall) hinside), hinverse]
      · rw [hCOutside 1 i theta hinside]
        have hover := hOverlap 1 (q i theta) hlevel htarget
          (by rw [hinverse, hnorm]; linarith only [ha.1])
          (by rw [hinverse, hnorm]; linarith only [ha.2])
        simpa only [hinverse, timeCut, j] using hover.symm
    have hangular : Fangular 1 x = Xbranch 0 (1 + a) k := by
      simpa only [x, timeCut, Real.smoothTransition.one, one_mul,
        neg_add_cancel, zero_div] using hAngular 1 k a ha
    have hFx : Fangular 1 x ∈ closedBall (0 : E2) 2 :=
      mem_closedBall_zero_iff.mpr (by rw [(hFNorm 1 x).1, hnorm]; linarith only [ha.2])
    calc
      C 1 i theta = Bwall.chart (Fangular 1 x) := hsame
      _ = horizontalBandProjection u (j (ks (Fangular 1 x))) :=
        (hCoordinates (Fangular 1 x) hFx).1.symm
      _ = horizontalBandProjection u (j (Eport k (0, a))) := by
        rw [hangular]
        have he := hPortNative k 0 a
          ⟨by linarith only [hdelta], by linarith only [hdelta]⟩ ha
        simpa only [zero_div] using congrArg (fun p => horizontalBandProjection u (j p)) he.symm
      _ = Bwall.chart ((1 + a) • port k) :=
        (hEport k).2.2.2.2.2.2.2.2.2.1 a ha
  let alphaT : Fin 2 → ℝ → E2 := fun i t =>
    C 1 (label i) (phase i (Theta i t))
  have hThetaOld (i : Fin 2) : MapsTo (Theta i)
      (Icc (-nu) (1 + nu)) (Icc (-eta) (1 + eta)) := by
    intro t ht
    have hm := (hTheta i).2.2.2.2.2.1 ht
    exact ⟨by linarith only [hm.1, heta1Old], by linarith only [hm.2, heta1Old]⟩
  obtain ⟨hTargetArcs, hTargetArcsDisjoint, hTargetPhaseImage⟩ :=
    saddle_selected_reparametrized_arcs q label angleNew speedNew
      (fun i => abs_pos.mp (hOrderedArcs i).1) (C 1)
      (hCEmbedding 1) (hCDisjoint 1) Theta eta nu
      (fun i => (hOrderedArcs i).2.2.2.2.1) hThetaOld
      (fun i => (hTheta i).2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hTargetStart (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (-nu) nu) :
      alphaT i t = Bwall.chart ((1 + t) • port (finProdFinEquiv (i, (0 : Fin 2)))) := by
    have hm := (hTheta i).2.2.2.2.2.2.1 ht
    obtain ⟨-, heq, ha⟩ := (hEndpoint i).2.2.2.2.2.2.2.2.1 (Theta i t) hm
    have hb : b0 i (Theta i t) = t := (hTheta i).2.2.2.2.2.2.2.2.1 ht
    simpa only [hb] using hCriticalPort _ (b0 i (Theta i t)) ha
      (label i) (phase i (Theta i t)) heq.symm
  have hTargetFinish (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (1 - nu) (1 + nu)) :
      alphaT i t = Bwall.chart ((2 - t) • port (finProdFinEquiv (i, (1 : Fin 2)))) := by
    have hm := (hTheta i).2.2.2.2.2.2.2.1 ht
    obtain ⟨-, heq, ha⟩ := (hEndpoint i).2.2.2.2.2.2.2.2.2 (Theta i t) hm
    have hb : 1 - b1 i (Theta i t) = t := (hTheta i).2.2.2.2.2.2.2.2.2.1 ht
    have hr : 1 + b1 i (Theta i t) = 2 - t := by linarith only [hb]
    simpa only [hr] using hCriticalPort _ (b1 i (Theta i t)) ha
      (label i) (phase i (Theta i t)) heq.symm
  let sign : Fin 2 → ℝ := ![1, -1]
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
    D.morse.symm (N (sign i * vv t, sign i * Real.sqrt ((vv t) ^ 2 + delta)))
  let Z : Fin 2 → Set E2 := fun i =>
    {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
  have hConnector : ∀ i : Fin 2, ks '' Z i = range (gamma i) :=
    saddle_selected_connector_image psi u D rho delta hrho hdelta hSmall J2 hJ2 N ks hksForm
  have hConnectorCover : La ∩ Dc = ⋃ i : Fin 2, range (gamma i) :=
    (saddle_selected_lower_hyperbola_arcs psi u D R delta hR hdelta hSmall hMorse N hN).2.2.2.1
  have hVDc : V ⊆ Dc := by
    apply image_mono
    intro s hs
    exact (show s.1 ^ 2 + s.2 ^ 2 < rho ^ 2 from hs).le
  have hCircleImages := saddle_selected_circle_images q label src gamma La Dc V
    hVDc hqLevel hqDisjoint
    (fun i p hp => by obtain ⟨t, rfl⟩ := hp; exact mem_range_self (phase i t))
    hRemovedParents hOrderedCover hConnectorCover ks Bwall.chart
    (fun x hx => hksBuffer ((closedBall_subset_closedBall (by norm_num)) hx))
    hClosedDisc Z (fun i x hx => mem_closedBall_zero_iff.mpr hx.1)
    hConnector (Fangular 1) (Alevel 1) (C 1) (hCglue 1)
    (fun p hp => ⟨(hGRegions 1 p hp).1.trans (Set.ext_iff.mp hOpenDisc p),
      (hGRegions 1 p hp).2.1.trans (Set.ext_iff.mp hClosedDisc p)⟩)
    (fun p hp hd => (hGRegions 1 p hp).2.2.1 (by rw [hClosedDisc]; exact hd))
  have hTargetImage (i : Fin 2) :
      alphaT i '' Icc (0 : ℝ) 1 = Alevel 1 '' (src i '' Icc (0 : ℝ) 1) := by
    rw [hTargetPhaseImage i]
    ext y
    constructor
    · rintro ⟨theta, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨src i t, ⟨t, ht, rfl⟩, (hCglue 1 (label i) (phase i t)).symm⟩
    · rintro ⟨p, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨phase i t, ⟨t, ht, rfl⟩, hCglue 1 (label i) (phase i t)⟩
  have hTargetProper (i : Fin 2) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      alphaT i t ∉ Bwall.chart '' closedBall (0 : E2) 1 := by
    have hpar : Theta i t ∈ Ioo (0 : ℝ) 1 := by
      rw [← (hTheta i).2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact ⟨t, ht, rfl⟩
    have hp : src i (Theta i t) ∈ La := by
      change H (j (src i (Theta i t))) = c - delta
      linarith only [hSrcLevel i (Theta i t)]
    intro hmem
    apply hSrcExterior i (Theta i t) hpar
    have himage : Alevel 1 (src i (Theta i t)) ∈
        Bwall.chart '' closedBall (0 : E2) 1 := by
      rw [← hCglue 1 (label i) (phase i (Theta i t))]
      exact hmem
    have hs := (hGRegions 1 (src i (Theta i t)) hp).2.1.mp himage
    rw [hClosedDisc] at hs
    exact hs
  have hTargetExterior : (⋃ i : Fin 2, alphaT i '' Icc (0 : ℝ) 1) =
      {x : E2 | L.symm (x, c) ∈ range j} \ (Bwall.chart '' ball (0 : E2) 1) := by
    have hlabel : (⋃ i : Fin 2, range (C 1 (label i))) =
        ⋃ i : Fin 2, range (C 1 i) :=
      label.surjective.iUnion_comp (fun i : Fin 2 => range (C 1 i))
    calc
      (⋃ i : Fin 2, alphaT i '' Icc (0 : ℝ) 1) =
          ⋃ i : Fin 2, range (C 1 (label i)) \ (Bwall.chart '' ball (0 : E2) 1) := by
        congr 1; funext i
        exact (hTargetImage i).trans (hCircleImages i).2.2.2.2.symm
      _ = (⋃ i : Fin 2, range (C 1 i)) \ (Bwall.chart '' ball (0 : E2) 1) := by
        rw [← iUnion_sdiff, hlabel]
      _ = _ := by
        simpa only [Real.smoothTransition.one, one_mul, sub_add_cancel] using hCExterior 1
  have hInitial (i : Fin 2) (theta : UnitCircle) :
      C 0 i theta = Tlower (c - delta)
        ((heightPlaneCoordinates u (psi (W.leg i (theta, W.level), 0))).1) := by
    rw [hCStart 0 i theta le_rfl]
    simpa only [L, c, H, j, InnerProductSpace.toDual_apply_apply,
      horizontalBandProjection_apply, ContinuousLinearEquiv.apply_symm_apply] using
      congrArg (fun y : E3 => (L y).1) (hqReconstruction i theta)
  have hbudget : 4 * delta < rho ^ 2 * beta := by
    have hd : delta ≤ epsilon / 8 := min_le_left _ _
    have he : epsilon ≤ rho ^ 2 * beta := min_le_right _ _
    have hp : 0 < rho ^ 2 * beta := mul_pos (sq_pos_of_pos hrho) hbeta
    linarith only [hd, he, hp]
  have hFinalCircle (i : Fin 2) : range (C 1 (label i)) =
      (alphaT i '' Icc (0 : ℝ) 1) ∪ (Bwall.chart '' ((Fangular 1) '' Z i)) := by
    rw [(hCircleImages i).2.2.1, ← hTargetImage i]
  have hTself (s : ℝ) (y : E3) : Phi (s - s) y = y := by
    simpa only [sub_self] using hPhiZero y
  have hElapsedDeriv (Y : E3 → E3) (k l : ℝ≥0) (hk : LipschitzWith k Y)
      (hl : ∀ y, ‖Y y‖ ≤ l) (s t : ℝ) (y : E3) :
      HasDerivAt (fun a => boundedFlow Y hk hl y (a - s))
        (Y (boundedFlow Y hk hl y (t - s))) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (boundedFlow_hasDerivAt Y hk hl y (t - s)).scomp t ((hasDerivAt_id t).sub_const s)
  have hTderiv (s t : ℝ) (y : E3) :
      HasDerivAt (fun a => Phi (a - s) y) (Xfield (Phi (t - s) y)) t :=
    hElapsedDeriv Xfield Klip Lbound hKlip hLbound s t y
  have hnuBound : nu < 1 / 16 := by linarith only [hnuSmall, heta1Small]
  refine ⟨rho, delta, hrho, hdelta, hSmall, J2, hJ2, Bwall.chart,
    Tlower (c - delta), C, label, nu, alphaT, Xfield, (fun s t => Phi (t - s)),
    hbudget, hLowerCut, hWallBuffer, Bwall.smooth, Bwall.smooth_symm,
    hC, hCEmbedding, hCDisjoint, hInitial, hnu, hnuBound, hTargetArcs,
    hTargetArcsDisjoint, hTargetProper, hTargetStart, hTargetFinish,
    hFinalCircle, hTargetExterior, hXfield, hTself, hTderiv, ?_⟩
  intro g hg
  obtain ⟨hGraph, hTrack⟩ := saddle_selected_middle_native
    psi u D R b delta hR hdelta hWindow hSmall P Araw hAsource hAgraph
    J2 hJ2 N (fun s => (hN s).2) Bwall.chart hWallForm g hg ks hksForm
    Xfield Klip Lbound hKlip hLbound hXfield hcXfield hCoordinates hNative
  refine ⟨hGraph, hTrack, ?_⟩
  let E : ℝ → Set E2 := fun t =>
    {x : E2 | L.symm (g x, c + t) ∈ range j ∧ 1 ≤ ‖x‖}
  let Ext : ℝ → Set E3 := fun t =>
    L.symm '' ((g '' E t) ×ˢ ({c + t} : Set ℝ))
  have hgBall : g '' ball (0 : E2) 1 = Bwall.chart '' ball (0 : E2) 1 := by
    apply image_congr
    intro x hx
    exact hg ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num))) hx)
  have hji : Function.Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hExt (t : ℝ) (ht : |t| ≤ 2 * delta) : Ext t = Elevel t := by
    apply saddle_middle_exterior_source_disc u c t g j V hji
    intro p hp
    simpa only [hgBall, hOpenDisc] using (hNoSheets t ht p hp).1
  intro s t hs ht
  change Phi (t - s) '' Ext s = Ext t ∧ (Phi (t - s)).symm '' Ext t = Ext s
  rw [hExt s hs, hExt t ht]
  exact hPhiExterior s t hs ht

end PoincareConjecture.M25.Topology3D
