import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedSourceChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedSourceGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedClosedCircleFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AngularReconnection
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace NNReal Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_wall_circle_family
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R b delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hsmall : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hwindow : 2 * delta < 8 * b)
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3)
    (hPsource : P.source =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2})
    (hPmorse : P.source ⊆ D.morse.target)
    (hPform : ∀ s ∈ P.source,
      P s = horizontalBandProjection u (psi (D.morse.symm s, 0)))
    (hAsource : A.source =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ×ˢ
        Ioo (⟪(u : E3), psi (D.point, 0)⟫_ℝ - 8 * b)
          (⟪(u : E3), psi (D.point, 0)⟫_ℝ + 8 * b))
    (hAform : ∀ w ∈ A.source,
      A w = (heightPlaneCoordinates u).symm (P w.1, w.2) ∧
      (A w ∈ range (fun p : UnitTwoSphere => psi (p, 0)) ↔
        w.2 = ⟪(u : E3), psi (D.point, 0)⟫_ℝ +
          D.morseSign1 * w.1.1 ^ 2 + D.morseSign2 * w.1.2 ^ 2))
    (hcore : ∀ p : UnitTwoSphere,
      |⟪(u : E3), psi (p, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → p ∈ D.sourceCore)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2)
    (kp : OpenPartialHomeomorph E2 E2)
    (hkpForm : ∀ x : E2, kp x = P (N ((5 * R / 8) • J2 x)))
    (hkpSource : closedBall (0 : E2) 2 ⊆ kp.source)
    (hkp : ContDiffOn ℝ ∞ kp kp.source)
    (hkpInv : ContDiffOn ℝ ∞ kp.symm kp.target)
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ p : UnitCircle, Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) p))
    (hqd : ∀ i k : Fin 2, i ≠ k → Disjoint (range (q i)) (range (q k)))
    (hqLevel : (⋃ i : Fin 2, range (q i)) =
      {p : UnitTwoSphere | ⟪(u : E3), psi (p, 0)⟫_ℝ =
        ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta})
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let pi := horizontalBandProjection u
    let L := heightPlaneCoordinates u
    let S := range j
    let rho := 5 * R / 8
    let hrho : 0 < rho := by dsimp [rho]; positivity
    let mu := delta / rho ^ 2
    let hmu : 0 < mu := div_pos hdelta (sq_pos_of_pos hrho)
    let hmuSmall : mu ≤ 1 / 128 :=
      (div_le_iff₀ (sq_pos_of_pos hrho)).mpr (by dsimp [rho]; linarith)
    let F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
    let Do : ℝ → Set UnitTwoSphere := fun r => D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    let Dc : ℝ → Set UnitTwoSphere := fun r => D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Elevel : ℝ → Set E3 := fun z =>
      (S ∩ {y | H y = c + z}) \ (j '' Do rho)
    let sigma : ℝ → ℝ := Real.smoothTransition
    let K := kp '' closedBall (0 : E2) 1
    let V := kp '' ball (0 : E2) 1
    ∃ (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
      (Xfield : E3 → E3) (Klip Lbound : ℝ≥0)
      (hKlip : LipschitzWith Klip Xfield)
      (hLbound : ∀ y, ‖Xfield y‖ ≤ Lbound)
      (hXfield : ContDiff ℝ ∞ Xfield) (hcXfield : HasCompactSupport Xfield),
    let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
      fun t => boundedFlowDiffeomorph Xfield hKlip hLbound hXfield hcXfield t
    ∃ (Csupport : Set E3) (C : ℝ → Fin 2 → UnitCircle → E2),
      ks.source = {x : E2 | N (rho • J2 x) ∈ D.morse.target} ∧
      ks.target = D.morse.source ∧
      (∀ x : E2, ks x = D.morse.symm (N (rho • J2 x))) ∧
      (∀ p : UnitTwoSphere,
        ks.symm p = J2.symm (rho⁻¹ • N.symm (D.morse p))) ∧
      closedBall (0 : E2) 2 ⊆ ks.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ks ks.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ks.symm ks.target ∧
      ks '' ball (0 : E2) 1 = Do rho ∧
      ks '' closedBall (0 : E2) 1 = Dc rho ∧
      (∀ x ∈ closedBall (0 : E2) 2,
        pi (j (ks x)) = kp x ∧
        H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2)) ∧
      (∀ z : ℝ, |z| ≤ 2 * delta → ∀ p : UnitTwoSphere,
        H (j p) = c + z →
        (pi (j p) ∈ V ↔ p ∈ ks '' ball (0 : E2) 1) ∧
        (pi (j p) ∈ K ↔ p ∈ ks '' closedBall (0 : E2) 1)) ∧
      IsCompact Csupport ∧ tsupport Xfield ⊆ Csupport ∧
      Csupport ⊆ ((psi '' (univ ×ˢ Ioo (-1) 1)) ∩
        {y : E3 | |H y - c| < 4 * delta}) \ (j '' Dc (rho / 4)) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
      (∀ y : E3, Phi 0 y = y) ∧
      (∀ t : ℝ,
        tsupport (fun y : E3 => Phi t y - y) ⊆ Csupport ∧
        tsupport (fun y : E3 => (Phi t).symm y - y) ⊆ Csupport) ∧
      (∀ t : ℝ, Phi t '' S = S ∧ (Phi t).symm '' S = S) ∧
      (∀ t : ℝ, ∀ y : E3,
        (y ∈ j '' Dc (rho / 4) ∨ 4 * delta ≤ |H y - c|) →
          Phi t y = y ∧ (Phi t).symm y = y) ∧
      (∀ p : UnitTwoSphere, |H (j p) - c| ≤ 3 * delta →
        p ∉ Do (rho / 2) → H (Xfield (j p)) = 1) ∧
      (∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
        Phi (t - s) '' Elevel s = Elevel t ∧
        (Phi (t - s)).symm '' Elevel t = Elevel s) ∧
      (∀ i : Fin 2,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
          (fun p : ℝ × UnitCircle => C p.1 i p.2)) ∧
      (∀ t i, IsPlanarEmbedding (C t i)) ∧
      (∀ t i k, i ≠ k → Disjoint (range (C t i)) (range (C t k))) ∧
      (∀ t i theta, t ≤ 0 → C t i theta = pi (j (q i theta))) ∧
      (∀ t i theta, 1 ≤ t → C t i theta = C 1 i theta) ∧
      (∀ t i theta, q i theta ∈ ks '' closedBall (0 : E2) 1 →
        C t i theta = kp (F t (ks.symm (q i theta)))) ∧
      (∀ t i theta, q i theta ∉ ks '' ball (0 : E2) 1 →
        C t i theta = pi (Phi (sigma t * delta) (j (q i theta)))) ∧
      (∀ t, (⋃ i : Fin 2, range (C t i)) \ V =
        {x : E2 | L.symm (x, c - delta + sigma t * delta) ∈ S} \ V) ∧
      (∀ t, (⋃ i : Fin 2, range (C t i)) ∩ K =
        kp '' ((F t) '' {x : E2 | ‖x‖ ≤ 1 ∧
          rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = -delta})) ∧
      (∀ i : Fin 2, Disjoint (range (q i)) (ks '' closedBall (0 : E2) 1) →
        (∀ t theta, C t i theta =
          pi (Phi (sigma t * delta) (j (q i theta)))) ∧
        ∀ t, Disjoint (range (C t i)) K) := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let rho := 5 * R / 8
  have hrho : 0 < rho := by dsimp [rho]; positivity
  let mu := delta / rho ^ 2
  have hmu : 0 < mu := div_pos hdelta (sq_pos_of_pos hrho)
  have hmuSmall : mu ≤ 1 / 128 :=
    (div_le_iff₀ (sq_pos_of_pos hrho)).mpr (by dsimp [rho]; linarith)
  let F := Classical.choose (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  let Do : ℝ → Set UnitTwoSphere := fun r => D.morse.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  let Elevel : ℝ → Set E3 := fun z =>
    (range j ∩ {y | H y = c + z}) \ (j '' Do rho)
  let sigma : ℝ → ℝ := Real.smoothTransition
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let X : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
    (sx i * Real.sqrt ((r ^ 2 + a) / 2),
      sy i * Real.sqrt ((r ^ 2 - a) / 2))
  obtain ⟨ks, hksSourceEq, hksTarget, hksForm, hksInverse, hksSource,
    hks, hksInv, hCoordinates, hNoSheets⟩ :=
    exists_saddle_selected_source_chart psi hpsi u D R b delta hR hwindow
      P A hPsource hPmorse hPform hAsource hAform J2 hJ2 N (fun s => (hN s).2)
      kp hkpForm
  obtain ⟨hOpenImage, hClosedImage, hBranch⟩ :=
    saddle_selected_source_geometry psi u D rho hrho J2 hJ2 N
      (fun s => (hN s).2.1) ks hksForm
  have hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target := by rw [← hPsource]; exact hPmorse
  obtain ⟨Xfield, Klip, Lbound, hKlip, hLbound, hXfield, hcXfield,
    Csupport, hCompact, hFieldSupport, hCarrier, hPhi, hPhiInv, hFlow,
    hSupport, hSphere, hFix, hHeight, _, _, _, _, _, hNative, hExterior⟩ :=
    exists_saddle_selected_wall_transport psi hpsi u D R delta hR hdelta
      hsmall hmorse hcore N hN
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => boundedFlowDiffeomorph Xfield hKlip hLbound hXfield hcXfield t
  have hPhiZero (y : E3) : Phi 0 y = y := boundedFlow_zero Xfield hKlip hLbound y
  change ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
    Phi (t - s) '' Elevel s = Elevel t ∧
    (Phi (t - s)).symm '' Elevel t = Elevel s at hExterior
  have hLower : |(-delta : ℝ)| ≤ 2 * delta := by
    rw [abs_neg, abs_of_pos hdelta]
    linarith
  have hTrackHeight (tau : ℝ) (htau : tau ∈ Icc (0 : ℝ) delta) :
      |-delta + tau| ≤ 2 * delta := abs_le.mpr ⟨by linarith [htau.1], by linarith [htau.2]⟩
  let Es : ℝ → Set E3 := fun z =>
    (range j ∩ {y | H y = c + z}) \ (j '' (ks '' ball (0 : E2) 1))
  have hEs (z : ℝ) : Es z = Elevel z := by
    dsimp only [Es, Elevel, Do]
    rw [hOpenImage]
  have hExteriorA2 : ∀ tau ∈ Icc (0 : ℝ) delta,
      Phi tau '' Es (-delta) = Es (-delta + tau) := by
    intro tau htau
    rw [hEs, hEs]
    have htime : -delta + tau - -delta = tau := by ring
    simpa only [htime] using
      (hExterior (-delta) (-delta + tau) hLower (hTrackHeight tau htau)).1
  have hNativeA2 : ∀ tau ∈ Icc (0 : ℝ) delta, ∀ i : Fin 4,
      ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
        Phi tau (j (ks (X (-delta / rho ^ 2) (1 + a) i))) =
          j (ks (X ((-delta + tau) / rho ^ 2) (1 + a) i)) := by
    intro tau htau i a ha
    change Phi tau (j (ks (J2.symm _))) = j (ks (J2.symm _))
    rw [hBranch (-delta) (1 + a) i, hBranch (-delta + tau) (1 + a) i]
    have htime : -delta + tau - -delta = tau := by ring
    simpa only [htime] using
      hNative i a (abs_lt.mpr ha) (-delta) (-delta + tau) hLower (hTrackHeight tau htau)
  obtain ⟨hF, _, _, hFNorm, hFZero, hFOne, _, _, hFX, _⟩ :=
    Classical.choose_spec (exists_saddle_angular_reconnection
      J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  change ∀ t i r, r ∈ Icc (3 / 4 : ℝ) (5 / 4) →
    F t (X (-mu) r i) = X (-(1 - sigma t) * mu) r i at hFX
  have hAngular : ∀ t : ℝ, ∀ i : Fin 4,
      ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
        F t (X (-delta / rho ^ 2) (1 + a) i) =
          X ((-delta + sigma t * delta) / rho ^ 2) (1 + a) i := by
    intro t i a ha
    have hstart : -delta / rho ^ 2 = -mu := by dsimp [mu]; ring
    have hend : (-delta + sigma t * delta) / rho ^ 2 =
        -(1 - sigma t) * mu := by dsimp [mu]; ring
    rw [hstart, hend]
    exact hFX t i (1 + a) ⟨by linarith [ha.1], by linarith [ha.2]⟩
  obtain ⟨C, hC, hEmbedding, hDisjoint, hStart, hEnd, hInside, hOutside,
    hExteriorImage, hInteriorImage, hBypass⟩ :=
    exists_saddle_selected_closed_circle_family psi hpsi u c rho delta hrho hdelta
      hsmall J2 hJ2 ks kp hksSource hkpSource hks hksInv hkp hkpInv 2 q hq hqd
      Phi hPhi hPhiZero F hF (fun t x => (hFNorm t x).1)
      (fun t x ht => (hFZero t x ht).1) (fun t x ht => (hFOne t x ht).1)
      hCoordinates hNoSheets hqLevel hExteriorA2 hNativeA2 hAngular
  exact ⟨ks, Xfield, Klip, Lbound, hKlip, hLbound, hXfield, hcXfield,
    Csupport, C, hksSourceEq, hksTarget, hksForm, hksInverse, hksSource,
    hks, hksInv, hOpenImage, hClosedImage, hCoordinates, hNoSheets,
    hCompact, hFieldSupport, hCarrier, hPhi, hPhiInv, hPhiZero, hSupport,
    hSphere, hFix, hHeight, hExterior, hC, hEmbedding, hDisjoint, hStart,
    hEnd, hInside, hOutside, hExteriorImage, hInteriorImage, hBypass⟩

end PoincareConjecture.M25.Topology3D
