import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RawPieceBandInput
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallGerms
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedLowerExteriorArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallCircleFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedComparisonFillings
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedOrientedExteriorArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedEndpointCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedConnectorImage
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedCircleImages
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedReparametrizedArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedPhysicalPair
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedReferencePlacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceExteriorStrip
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceComparisonFillings
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedMiddleNative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceMiddleNative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MiddleExteriorCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonMiddleIsotopy

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix NNReal

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

set_option maxHeartbeats 400000 in

theorem exists_saddle_nonnested_raw_middle
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let L := heightPlaneCoordinates u
    ∃ (sigma : ℝ) (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
      (rho a delta e : ℝ) (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
      (gRef : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (Aref : Diffeomorph 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, E3)
        ((ℝ × ℝ) × ℝ) E3 ∞)
      (G : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C3 : Set E3),
      let Fref := (nonnestedReferenceDiffeomorph 0 d hd).trans Aref
      let S : Fin 2 → Set E3 :=
        ![range (fun q : UnitTwoSphere => Fref (q : E3)), range j]
      0 < sigma ∧ sigma ≤ 1 / 16 ∧ HasCompactSupport d ∧
      tsupport d ⊆ Ioo (-sigma) sigma ∧
      (∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
        d q = Real.sqrt (1 - q) - 1 + q / 2) ∧
      (∀ q : ℝ, sigma ≤ q → d q = 0) ∧
      (∀ q : ℝ, 0 ≤ q → -(q ^ 2) / 2 ≤ d q ∧ d q ≤ 0) ∧
      (∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16) ∧
      0 < rho ∧ 0 < a ∧ 16 / sigma < a ^ 2 ∧ 8 < a ^ 2 ∧
      4 / a ^ 2 < sigma / 4 ∧ 1 / a ^ 2 < 1 / 8 ∧
      (∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2) ∧
      (∀ p : (ℝ × ℝ) × ℝ,
        Aref p = L.symm (gRef (a • J2.symm p.1), c + rho ^ 2 * a ^ 2 * p.2)) ∧
      (∀ y : E3, Aref.symm y =
        (J2 (a⁻¹ • gRef.symm (L y).1), ((L y).2 - c) / (rho ^ 2 * a ^ 2))) ∧
      (∀ p : (ℝ × ℝ) × ℝ, H (Aref p) = c + rho ^ 2 * a ^ 2 * p.2) ∧
      S 0 = Aref '' (nonnestedReferenceBallChart 0 d hd).boundary ∧
      0 < delta ∧ W.level < c - delta ∧ delta ≤ rho ^ 2 / 128 ∧
      0 < e ∧ e < 1 / 512 ∧ IsCompact C3 ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (G p.1).symm p.2) ∧
      (∀ y : E3, G 0 y = y ∧ (G 0).symm y = y) ∧
      (∀ (s : ℝ) (y : E3), H (G s y) = H y ∧ H ((G s).symm y) = H y) ∧
      (∀ s : ℝ, tsupport (fun y : E3 => G s y - y) ⊆ C3 ∧
        tsupport (fun y : E3 => (G s).symm y - y) ⊆ C3) ∧
      (∀ (s : ℝ) (x : E2) (z : ℝ), ‖x‖ ≤ 1 + 2 * e →
        G s (L.symm (gRef x, z)) = L.symm (gRef x, z) ∧
        (G s).symm (L.symm (gRef x, z)) = L.symm (gRef x, z)) ∧
      (∀ t : ℝ, |t| ≤ delta →
        G 1 '' (S 0 ∩ {y : E3 | H y = c + t}) =
          S 1 ∩ {y : E3 | H y = c + t} ∧
        (G 1).symm '' (S 1 ∩ {y : E3 | H y = c + t}) =
          S 0 ∩ {y : E3 | H y = c + t}) ∧
      G 1 '' (S 0 ∩ {y : E3 | |H y - c| ≤ delta}) =
        S 1 ∩ {y : E3 | |H y - c| ≤ delta} ∧
      (G 1).symm '' (S 1 ∩ {y : E3 | |H y - c| ≤ delta}) =
        S 0 ∩ {y : E3 | |H y - c| ≤ delta} ∧
      G 1 '' (S 0 ∩ {y : E3 | |H y - c| < delta}) =
        S 1 ∩ {y : E3 | |H y - c| < delta} ∧
      (G 1).symm '' (S 1 ∩ {y : E3 | |H y - c| < delta}) =
        S 0 ∩ {y : E3 | |H y - c| < delta} := by
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
  let delta := min ((b / 8) / 8) (min ((c - W.level) / 4) (rho ^ 2 / 128))
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
    exists_saddle_selected_wall_germs psi hpsi u D W R b (b / 8) hR hb
      (by positivity) le_rfl P Araw hPsource hPs hPi hPmorse hPform hAsource hAgraph
  have hSmall : delta ≤ (5 * R / 8) ^ 2 / 128 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hCoreBand (q : UnitTwoSphere) (hq : |H (j q) - c| ≤ 3 * delta) :
      q ∈ D.sourceCore := by
    apply hCore q
    have hd : 2 * delta < b / 8 := hdeltaB
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
  obtain ⟨chi, hchi, hchiCompact, hchiSupport, hchiNear, hchiBounds⟩ :=
    exists_compact_smooth_cutoff (K := Icc (3 / 4 : ℝ) (5 / 4))
      (U := Ioo (1 / 2 : ℝ) (3 / 2)) isCompact_Icc isOpen_Ioo
      (by intro r hr; exact ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hchiOne (r : ℝ) (hr : r ∈ Icc (3 / 4 : ℝ) (5 / 4)) : chi r = 1 :=
    subset_of_mem_nhdsSet hchiNear hr
  have hrho : 0 < rho := by dsimp only [rho]; positivity
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
  obtain ⟨Pfamily, Gfamily, hFamilyBoundary, hFamilyInitial, hFamilyDisjoint⟩ :=
    exists_saddle_selected_comparison_fillings hP psi u D W hnonnested
      (Tlower (c - delta)) C hC (fun t _ i => hCEmbedding t i)
      (fun t _ => hCDisjoint t 0 1 (by decide)) hInitial
  let Btarget : Fin 2 → BallNeighborhoodChart E2 E2 := fun i =>
    (Gfamily (label i)).fiberBallNeighborhood 1 ⟨zero_le_one, le_rfl⟩
  have hTargetBoundary (i : Fin 2) : (Btarget i).boundary =
      (alphaT i '' Icc (0 : ℝ) 1) ∪ (Bwall.chart '' ((Fangular 1) '' Z i)) := by
    rw [hFamilyBoundary 1 ⟨zero_le_one, le_rfl⟩ (label i),
      (hCircleImages i).2.2.1, hTargetImage i]
  have hTargetCase : Disjoint (Btarget 0).closedRegion (Btarget 1).closedRegion := by
    have hne : label 0 ≠ label 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (label.injective h)
    have hd := hFamilyDisjoint 1 ⟨zero_le_one, le_rfl⟩
    dsimp only [Btarget]
    generalize hi : label 0 = i at hne ⊢
    generalize hk : label 1 = k at hne ⊢
    fin_cases i <;> fin_cases k
    · exact False.elim (hne rfl)
    · exact hd
    · exact hd.symm
    · exact False.elim (hne rfl)

  obtain ⟨sigma, d, hsigma, hsigmaSmall, hd, hdCompact, hdSupport,
    hdNear, hdZero, hdBounds, hdDeriv⟩ := exists_reference_ball_radial_correction
  obtain ⟨aRef, gRef, Aref, haRef, haCorrection, haLarge, haLocal, haUnit,
    hgRef, hgRefInv, hgRefImage, hAref, hArefInv, hArefHeight,
    hArefSmooth, hArefInvSmooth, hFrefSmooth, hFrefInvSmooth, hFref, hFrefInv,
    hBRefChart, hBRefSource, hBRefTarget, hBRefInside, hBRefClosed,
    hBRefBoundary, hBRefRegions, hLocalArefInv, hLocalArefRadius,
    hLocalArefHeight, hLocalBRef⟩ :=
    exists_saddle_nonnested_reference_placement Bwall.chart hWallBuffer
      Bwall.smooth Bwall.smooth_symm J2 hJ2 u c rho hrho sigma d hd
      hsigma hsigmaSmall hdNear
  obtain ⟨etaRef, QRef, hetaRef, hetaRefSmall, hQRef, hQRefProduct,
    hQRefClosed, hRefRegular, hRefLevels, hRefRadial, nuRef, ThetaRef,
    hnuRef, hnuRefSmall, hRefArcs, hRefArcsDisjoint, hRefExterior,
    hRefArcInverse⟩ :=
    exists_nonnested_reference_exterior_strip sigma hsigma hsigmaSmall
      d hd hdNear hdZero hdBounds hdDeriv J2 hJ2 aRef haRef haCorrection haLarge
  let alphaRef : Fin 2 → ℝ → E2 := fun i t =>
    aRef • J2.symm ((QRef i (ThetaRef i t, 0) : E3) 0 / Real.sqrt 2,
      (QRef i (ThetaRef i t, 0) : E3) 1 / Real.sqrt 2)
  let refSign : Fin 2 → ℝ := ![1, -1]
  have hRefPorts :
      (![J2.symm (1 / Real.sqrt 2, 1 / Real.sqrt 2),
        J2.symm (-1 / Real.sqrt 2, 1 / Real.sqrt 2),
        J2.symm (-1 / Real.sqrt 2, -1 / Real.sqrt 2),
        J2.symm (1 / Real.sqrt 2, -1 / Real.sqrt 2)] : Fin 4 → E2) = port := by
    funext k
    fin_cases k <;> rfl
  have hReferenceArcPacket (i : Fin 2) :
      ContDiffOn ℝ ∞ (alphaRef i) (Ioo (-nuRef) (1 + nuRef)) ∧
      InjOn (alphaRef i) (Ioo (-nuRef) (1 + nuRef)) ∧
      (∀ t ∈ Ioo (-nuRef) (1 + nuRef), deriv (alphaRef i) t ≠ 0) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 < refSign i * (J2 (alphaRef i t)).2) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, 1 < ‖alphaRef i t‖) ∧
      (∀ t : ℝ, |t| < nuRef →
        alphaRef i t = (1 + t) • port (finProdFinEquiv (i, (0 : Fin 2)))) ∧
      (∀ t : ℝ, |t - 1| < nuRef →
        alphaRef i t = (2 - t) • port (finProdFinEquiv (i, (1 : Fin 2)))) := by
    obtain ⟨_, _, _, _, _, _, _, hsm, hinj, hreg, hsign, hproper,
      hstart, hfinish⟩ := hRefArcs i
    refine ⟨hsm, hinj, hreg, hsign, hproper, ?_, ?_⟩
    · intro t ht
      simpa only [hRefPorts] using hstart t ht
    · intro t ht
      simpa only [hRefPorts] using hfinish t ht
  have hnuRefBound : nuRef < 1 / 16 := by linarith
  obtain ⟨cRef, BRefComparison, hcRef, hcRefImage, hBRefComparison,
    hBRefHalfPlane, hBRefDisjoint⟩ :=
    exists_nonnested_reference_comparison_fillings hP J2 hJ2
      (delta / rho ^ 2) hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne
      nuRef hnuRef hnuRefBound alphaRef
      (fun i => (hReferenceArcPacket i).1)
      (fun i => (hReferenceArcPacket i).2.1)
      (fun i => (hReferenceArcPacket i).2.2.1)
      (fun i => (hReferenceArcPacket i).2.2.2.1)
      (fun i => (hReferenceArcPacket i).2.2.2.2.1)
      (fun i => (hReferenceArcPacket i).2.2.2.2.2.1)
      (fun i => (hReferenceArcPacket i).2.2.2.2.2.2)
  obtain ⟨lPair, rPair, etaPair, CJ, J, hPair⟩ :=
    exists_saddle_selected_physical_pair hP Bwall.chart hWallBuffer
      Bwall.smooth Bwall.smooth_symm gRef hgRef J2 hJ2 mu hmu hmuSmall
      chi hchi hchiBounds hchiSupport hchiOne
      nu hnu alphaT hTargetArcs hTargetArcsDisjoint hTargetProper
      hTargetStart hTargetFinish Btarget hTargetBoundary hTargetCase
      nuRef hnuRef hnuRefBound alphaRef hReferenceArcPacket hRefArcsDisjoint
      cRef BRefComparison hcRefImage hBRefComparison hBRefDisjoint
  obtain ⟨hTargetGraph, hTargetTrack⟩ := saddle_selected_middle_native
    psi u D R b delta hR hdelta hWindow hSmall P Araw hAsource hAgraph
    J2 hJ2 N (fun s => (hN s).2) Bwall.chart hWallForm gRef hgRef ks hksForm
    Xfield Klip Lbound hKlip hLbound hXfield hcXfield hCoordinates hNative
  let Fref : D3 := (nonnestedReferenceDiffeomorph 0 d hd).trans Aref
  let Bref := (nonnestedReferenceBallChart 0 d hd).mapDiffeomorph Aref
  let jRef : UnitTwoSphere → E3 := fun p => Fref (p : E3)
  let Sref : Set E3 := range jRef
  let Lambda := rho ^ 2 * aRef ^ 2
  let betaRef := 1 / (128 * aRef ^ 2)
  let fRef : UnitTwoSphere → ℝ := fun p => 1 + (p : E3) 2 - ((p : E3) 1) ^ 2 +
    d (((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2)
  let qRef : UnitTwoSphere → ℝ := fun p => ((p : E3) 0) ^ 2 + ((p : E3) 1) ^ 2
  let rRef : E3 → E2 := fun p => aRef • J2.symm (p 0 / Real.sqrt 2, p 1 / Real.sqrt 2)
  let Eref : ℝ → Set E3 := fun t => jRef '' {p | fRef p = t ∧ 2 / aRef ^ 2 ≤ qRef p}
  have hLambda : 0 < Lambda := mul_pos (sq_pos_of_pos hrho) (sq_pos_of_pos haRef)
  have hRefHeight (p : UnitTwoSphere) : ⟪(u : E3), Fref p⟫_ℝ = c + Lambda * fRef p := by
    rw [hFref, hArefHeight]
  obtain ⟨zetaRef, Xref, Kref, BoundRef, hKref, hBoundRef, hXref, hcXref, Cref,
    hzetaRef, hzetaRefSmall, hCref, hXrefSupport, hCarrierRef, hPhiRef, hPhiRefInv,
    hPhiRefZero, hPhiRefForm, hPhiRefSupport, hPhiRefRadius, hPhiRefRegions,
    hPhiRefTargets, hPhiRefFix, hRefUnitHeight, hAmbientRefLevels, hRefWall,
    hRefDerivative, hRefNativeFlow, hRefImages⟩ :=
    exists_nonnested_reference_ambient_transport sigma hsigma hsigmaSmall d hd hdNear
      hdZero hdBounds hdDeriv aRef haRef haCorrection haLarge u c rho hrho Fref hRefHeight
  let PhiRef : ℝ → D3 := fun t => boundedFlowDiffeomorph Xref hKref hBoundRef hXref hcXref t
  have hRefParam (p : UnitTwoSphere) :
      jRef p = L.symm (gRef (rRef p), c + Lambda * fRef p) :=
    (hFref (p : E3)).trans (hAref _)
  have hRefPlanar (y : E3) : horizontalBandProjection u (Fref y) = gRef (rRef y) := by
    have he := congrArg (horizontalBandProjection u) ((hFref y).trans (hAref _))
    simpa only [horizontalBandProjection_apply, ContinuousLinearEquiv.apply_symm_apply] using he
  obtain ⟨hRefPoint, hReferenceTrack⟩ := saddle_reference_middle_native_tracks
    u c rho delta aRef hrho haRef hSmall J2 gRef Fref hRefPlanar Xref
    (fun k r hr h hh => (hRefWall k r hr h hh).2)
    (fun k r hr h hh => by
      simpa only [add_zero, one_smul] using
        hRefDerivative k r hr h 0 hh (by simpa only [abs_zero] using hzetaRef.le))
  have hRefBoundary : Sref = Bref.boundary := by
    rw [BallNeighborhoodChart.boundary, hBRefChart]
    change range jRef = Fref '' sphere (0 : E3) 1
    ext y; constructor
    · rintro ⟨p, rfl⟩; exact ⟨p, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
  have hReferenceGraph (t : ℝ) (ht : |t| < 2 * delta) (x : E2) (hx : ‖x‖ < 2) :
      L.symm (gRef x, c + t) ∈ Sref ↔ t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) := by
    have hx2 := mem_closedBall_zero_iff.mpr hx.le
    have hs : delta ≤ rho ^ 2 / 128 := hSmall
    have hh : |c + t - c| < rho ^ 2 := by
      rw [add_sub_cancel_left]; nlinarith only [ht, hs, sq_pos_of_pos hrho]
    have hb := (hLocalBRef x hx2 (c + t) hh).2.2
    rw [← hgRef hx2] at hb
    rw [hRefBoundary]
    exact hb.trans (by constructor <;> intro he <;> linarith only [he])
  let Sambient : Fin 2 → Set E3 := ![Sref, range j]
  let Xambient : Fin 2 → E3 → E3 := ![Xref, Xfield]
  let E : Fin 2 → ℝ → Set E2 := fun k t =>
    {x | L.symm (gRef x, c + t) ∈ Sambient k ∧ 1 ≤ ‖x‖}
  let Ext : Fin 2 → ℝ → Set E3 := fun k t =>
    L.symm '' ((gRef '' E k t) ×ˢ ({c + t} : Set ℝ))
  have hgBall := hgRefImage (ball (0 : E2) 1)
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))
  have hji : Function.Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hExtTarget (t : ℝ) (ht : |t| ≤ 2 * delta) : Ext 1 t = Elevel t := by
    apply saddle_middle_exterior_source_disc u c t gRef j V hji
    intro p hp
    simpa only [hgBall, hOpenDisc] using (hNoSheets t ht p hp).1
  have hRadius (p : UnitTwoSphere) : 1 ≤ ‖rRef p‖ ↔ 2 / aRef ^ 2 ≤ qRef p := by
    have hn : ‖rRef p‖ ^ 2 = aRef ^ 2 / 2 * qRef p := by
      rw [← hJ2]
      simp only [rRef, map_smul, ContinuousLinearEquiv.apply_symm_apply,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, div_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp only [qRef]; ring
    rw [div_le_iff₀ (sq_pos_of_pos haRef)]
    constructor <;> intro hh <;> nlinarith only [hn, hh, norm_nonneg (rRef p)]
  have hExtReference (t : ℝ) : Ext 0 t = Eref (t / Lambda) := by
    have he := saddle_middle_exterior_scaled_source u c t Lambda hLambda.ne'
      gRef jRef fRef (fun p => rRef p) hRefParam
    change Ext 0 t = jRef '' {p | fRef p = t / Lambda ∧ 1 ≤ ‖rRef p‖} at he
    rw [he]; congr 1; ext p
    exact and_congr Iff.rfl (hRadius p)
  have hScaled (t : ℝ) (ht : |t| ≤ 2 * delta) : |t / Lambda| ≤ 2 * betaRef := by
    rw [abs_div, abs_of_pos hLambda, div_le_iff₀ hLambda]
    have he : 2 * betaRef * Lambda = rho ^ 2 / 64 := by
      dsimp only [betaRef, Lambda]; field_simp; ring
    rw [he]; have hs : delta ≤ rho ^ 2 / 128 := hSmall; linarith only [ht, hs]
  let Tamb : Fin 2 → ℝ → ℝ → D3 :=
    ![fun s t => PhiRef (t - s), fun s t => Phi (t - s)]
  have hTself (k : Fin 2) (s : ℝ) (y : E3) : Tamb k s s y = y := by
    fin_cases k
    · change PhiRef (s - s) y = y
      simpa only [sub_self] using hPhiRefZero y
    · change Phi (s - s) y = y
      simpa only [sub_self] using hPhiZero y
  have hElapsed (s t : ℝ) : Lambda * (t / Lambda - s / Lambda) = t - s := by
    field_simp
  have hTimage (k : Fin 2) (s t : ℝ) (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta) :
      (Tamb k s t) '' Ext k s = Ext k t ∧ (Tamb k s t).symm '' Ext k t = Ext k s := by
    fin_cases k
    · change (PhiRef (t - s)) '' Ext 0 s = Ext 0 t ∧
        (PhiRef (t - s)).symm '' Ext 0 t = Ext 0 s
      rw [hExtReference, hExtReference]
      have he := (hRefImages (s / Lambda) (t / Lambda) (hScaled s hs) (hScaled t ht)).2
      change (PhiRef (Lambda * (t / Lambda - s / Lambda))) '' Eref (s / Lambda) =
        Eref (t / Lambda) ∧ (PhiRef (Lambda * (t / Lambda - s / Lambda))).symm ''
          Eref (t / Lambda) = Eref (s / Lambda) at he
      simpa only [hElapsed] using he
    · change (Phi (t - s)) '' Ext 1 s = Ext 1 t ∧ (Phi (t - s)).symm '' Ext 1 t = Ext 1 s
      rw [hExtTarget s hs, hExtTarget t ht]
      exact hPhiExterior s t hs ht
  have hElapsedDeriv (Y : E3 → E3) (k l : ℝ≥0) (hk : LipschitzWith k Y)
      (hl : ∀ y, ‖Y y‖ ≤ l) (s t : ℝ) (y : E3) :
      HasDerivAt (fun a => boundedFlow Y hk hl y (a - s))
        (Y (boundedFlow Y hk hl y (t - s))) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (boundedFlow_hasDerivAt Y hk hl y (t - s)).scomp t ((hasDerivAt_id t).sub_const s)
  have hTtrack (k : Fin 2) (s : ℝ) (_hs : |s| < 2 * delta)
      (y : E3) (_hy : y ∈ Ext k s) (t : ℝ) (_ht : |t| < 2 * delta) :
      HasDerivAt (fun a => Tamb k s a y) (Xambient k (Tamb k s t y)) t := by
    fin_cases k
    · exact hElapsedDeriv Xref Kref BoundRef hKref hBoundRef s t y
    · exact hElapsedDeriv Xfield Klip Lbound hKlip hLbound s t y
  rcases hPair with ⟨-, -, -, -, -, -, -, -, -, hCJ, hJ, hJinv, hJzero,
    hJone, hJsupport, hJfix, hCJopen, hJprotected, hJtails, hJpointwise, hJimages⟩
  have hJdisc : gRef '' closedBall (0 : E2) 1 ⊆ CJᶜ := by
    rw [hgRefImage _ (closedBall_subset_closedBall (by norm_num))]; exact hJprotected
  have hCriticalTarget : gRef '' E 1 0 = ⋃ i : Fin 2, alphaT i '' Icc (0 : ℝ) 1 := by
    have he := (saddle_middle_exterior_coordinates u c gRef (range j)).2 0
    change gRef '' E 1 0 = {v | L.symm (v, c + 0) ∈ range j} \ gRef '' ball (0 : E2) 1 at he
    simpa only [add_zero, hgBall, hTargetExterior] using he
  have hAi0 (x : E2) : Aref.symm (L.symm (gRef x, c)) =
      (((J2 x).1 / aRef, (J2 x).2 / aRef), 0) := by
    rw [hArefInv]
    simp only [L, ContinuousLinearEquiv.apply_symm_apply, gRef.symm_apply_apply,
      sub_self, zero_div, map_smul]
    congr 1
    exact Prod.ext (by simp only [Prod.smul_fst, smul_eq_mul, div_eq_mul_inv, mul_comm])
      (by simp only [Prod.smul_snd, smul_eq_mul, div_eq_mul_inv, mul_comm])
  have hCriticalReference : gRef '' E 0 0 =
      ⋃ i : Fin 2, (fun t => gRef (alphaRef i t)) '' Icc (0 : ℝ) 1 := by
    have he : E 0 0 = ⋃ i : Fin 2, alphaRef i '' Icc (0 : ℝ) 1 := by
      rw [hRefExterior]; ext x
      change (L.symm (gRef x, c + 0) ∈ Sref ∧ 1 ≤ ‖x‖) ↔ _
      rw [add_zero, hRefBoundary, hBRefBoundary,
        mem_image_iff_of_inverse Aref.symm_apply_apply Aref.apply_symm_apply, hAi0]
      exact and_comm
    rw [he, image_iUnion]; simp only [image_image]
  have hJimage : (J 1) '' (gRef '' E 0 0) = gRef '' E 1 0 ∧
      (J 1).symm '' (gRef '' E 1 0) = gRef '' E 0 0 := by
    rw [hCriticalReference, hCriticalTarget, image_iUnion, image_iUnion]
    constructor <;> congr 1 <;> funext i
    · exact (hJimages i).1
    · exact (hJimages i).2
  have hSambient (k : Fin 2) : IsCompact (Sambient k) := by
    fin_cases k
    · exact isCompact_range (Fref.continuous.comp continuous_subtype_val)
    · exact isCompact_range (collar_central_contMDiff psi hpsi).continuous
  obtain ⟨eMiddle, Gmiddle, Cmiddle, heMiddle, heMiddleSmall, hCmiddle,
    hGmiddle, hGmiddleInv, hGmiddleZero, hGmiddleHeight, hGmiddleSupport,
    hGmiddleDisc, hGmiddleLevels, hGmiddleClosed, hGmiddleClosedInv,
    hGmiddleOpen, hGmiddleOpenInv⟩ := exists_saddle_common_middle_isotopy
      u c rho delta hrho hdelta hSmall J2 hJ2 gRef Xambient
      (by intro k; fin_cases k <;> first | exact hXref | exact hXfield) Sambient hSambient
      (by intro k; fin_cases k <;> first | exact hReferenceGraph | exact hTargetGraph)
      (by intro k; fin_cases k <;> first | exact hReferenceTrack | exact hTargetTrack)
      Tamb hTself hTtrack hTimage J CJ hCJ hJ hJinv hJzero hJone hJsupport hJdisc hJimage
  exact ⟨sigma, d, hd, rho, aRef, delta, eMiddle, J2, gRef, Aref, Gmiddle, Cmiddle,
    hsigma, hsigmaSmall, hdCompact, hdSupport, hdNear, hdZero, hdBounds, hdDeriv,
    hrho, haRef, haCorrection, haLarge, haLocal, haUnit, hJ2, hAref, hArefInv,
    hArefHeight, hRefBoundary.trans hBRefBoundary, hdelta, hLowerCut, hSmall,
    heMiddle, heMiddleSmall, hCmiddle, hGmiddle, hGmiddleInv, hGmiddleZero,
    hGmiddleHeight, hGmiddleSupport, hGmiddleDisc, hGmiddleLevels,
    hGmiddleClosed, hGmiddleClosedInv, hGmiddleOpen, hGmiddleOpenInv⟩

end PoincareConjecture.M25.Topology3D
