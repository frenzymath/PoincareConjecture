import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RawPieceBandInput
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RelativeBand
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightPreservingCases
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

set_option maxHeartbeats 3000000 in

set_option maxRecDepth 4000 in



theorem exists_raw_saddle_piece_band_verticalization
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c : ℝ := H (j D.point)
    let S : Set E3 := range j
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let Q : ℝ × ℝ → ℝ := fun s =>
      D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
    let B : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    ∃ (R b epsilon : ℝ)
      (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
      (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3)
      (I : ℝ → D3) (Csupport : Set E3)
      (hR : 0 < R) (hb : 0 < b) (hepsilon : 0 < epsilon)
      (hheight : ∀ s : ℝ, ∀ y : E3,
        ⟪(u : E3), I s y⟫_ℝ = ⟪(u : E3), y⟫_ℝ ∧
        ⟪(u : E3), (I s).symm y⟫_ℝ = ⟪(u : E3), y⟫_ℝ),
    let r : ℕ → ℝ := fun i => (((i : ℝ) + 1) / 8) * R
    let V : ℕ → Set E2 := fun i => P '' Do (r i)
    let K := I 1
    let hK := fun y => (hheight 1 y).1
    let psiNew : UnitTwoSphere × ℝ → E3 := fun p => K (psi p)
    let Dnew := D.mapHeightPreserving K hK
    let Snew : Set E3 := range (fun q : UnitTwoSphere => psiNew (q, 0))
    let F := heightPreservingSliceDiffeomorph u K hK
    let Gamma : Set E2 := {x | L.symm (x, c) ∈ S}
    let Anew := A.trans K.toHomeomorph.toOpenPartialHomeomorph
    let U6 : Set ((ℝ × ℝ) × ℝ) := Do (r 6) ×ˢ Ioo (c - 4 * b) (c + 4 * b)
    let hU6 : IsOpen U6 :=
      (morseRadialDisc_geometry (r 6) (by dsimp [r]; positivity)).1.prod isOpen_Ioo
    let A6 := Anew.restrOpen U6 hU6
    let O : Set (E2 × ℝ) :=
      (V 5 \ closure (V 4)) ×ˢ Ioo (c - epsilon) (c + epsilon)
    epsilon ≤ b / 8 ∧ epsilon ≤ (r 0) ^ 2 / 8 ∧
    P.source = Do (2 * R) ∧
    A.source = Do (2 * R) ×ˢ Ioo (c - 8 * b) (c + 8 * b) ∧
    ContDiffOn ℝ ∞ P P.source ∧ ContDiffOn ℝ ∞ P.symm P.target ∧
    ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
    P.source ⊆ D.morse.target ∧
    (∀ s ∈ P.source, D.morse.symm s ∈ D.protectedSet ∧
      P s = pi (j (D.morse.symm s))) ∧
    P 0 = pi (j D.point) ∧ A (0, c) = j D.point ∧
    A.target = L.symm '' (P.target ×ˢ Ioo (c - 8 * b) (c + 8 * b)) ∧
    (∀ w ∈ A.source, A w = L.symm (P w.1, w.2) ∧ H (A w) = w.2 ∧
      (A w ∈ S ↔ w.2 = c + Q w.1)) ∧
    (∀ y ∈ A.target, A.symm y = (P.symm (pi y), H y)) ∧
    B R ⊆ P.source ∧ B R ×ˢ Icc (c - 4 * b) (c + 4 * b) ⊆ A.source ∧
    (∀ i : Fin D.capCount, ∀ y ∈ (D.cap i).cap, 8 * b < |H y - c|) ∧
    (∀ q : UnitTwoSphere, |H (j q) - c| ≤ 8 * b → q ∈ D.sourceCore) ∧
    (∀ i : ℕ, i ≤ 6 → IsOpen (V i) ∧ IsCompact (closure (V i)) ∧
      closure (V i) = P '' B (r i)) ∧
    (∀ i k : ℕ, i < k → k ≤ 6 → closure (V i) ⊆ V k) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E3 => I p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E3 => (I p.1).symm p.2) ∧
    (∀ y, I 0 y = y) ∧ IsCompact Csupport ∧
    Csupport ⊆ {y : E3 | |H y - c| < 2 * epsilon} ∧
    (∀ s : ℝ, tsupport (fun y => I s y - y) ⊆ Csupport ∧
      tsupport (fun y => (I s).symm y - y) ⊆ Csupport) ∧
    (∀ s y, (pi y ∈ closure (V 0) ∨ H y = c ∨ 2 * epsilon ≤ |H y - c|) →
      I s y = y ∧ (I s).symm y = y) ∧
    (∀ s : ℝ, IsCollarEmbedding (fun p => I s (psi p))) ∧
    IsCollarEmbedding psiNew ∧
    (∀ p : UnitTwoSphere × ℝ, K.symm (psiNew p) = psi p) ∧
    (∀ p : UnitTwoSphere × ℝ, H (psiNew p) = H (psi p)) ∧
    Snew = K '' S ∧ K.symm '' Snew = S ∧
    psiNew (Dnew.point, 0) = j D.point ∧
    Dnew.capCount = D.capCount ∧
    (∀ i : Fin D.capCount, Dnew.cap i = (D.cap i).mapHeightPreserving K hK) ∧
    Dnew.sourceCore = D.sourceCore ∧ Dnew.point = D.point ∧
    Dnew.slabLower = D.slabLower ∧ Dnew.slabUpper = D.slabUpper ∧
    Dnew.morse = D.morse ∧ Dnew.morseSign1 = D.morseSign1 ∧
    Dnew.morseSign2 = D.morseSign2 ∧ Dnew.protectedSet = D.protectedSet ∧
    Dnew.cutRadius = D.cutRadius ∧
    (∀ i : Fin D.capCount,
      (Dnew.cap i).sourceCap = (D.cap i).sourceCap ∧
      (Dnew.cap i).sourceSeam = (D.cap i).sourceSeam ∧
      (Dnew.cap i).cap = (D.cap i).cap ∧ (Dnew.cap i).seam = (D.cap i).seam ∧
      (Dnew.cap i).tube.source = (D.cap i).tube.source ∧
      (Dnew.cap i).tube.target = K '' (D.cap i).tube.target ∧
      (∀ p : E2 × ℝ, (Dnew.cap i).tube p = K ((D.cap i).tube p)) ∧
      (∀ y : E3, (Dnew.cap i).tube.symm y = (D.cap i).tube.symm (K.symm y)) ∧
      (∀ T : Set (E2 × ℝ), (Dnew.cap i).tube '' T =
        K '' ((D.cap i).tube '' T))) ∧
    (∀ s : ℝ, ∀ i : Fin D.capCount, ∀ y ∈ (D.cap i).cap,
      I s y = y ∧ (I s).symm y = y) ∧
    (Dnew.nonnested ↔ D.nonnested) ∧ (Dnew.nested ↔ D.nested) ∧
    (∀ W : SaddleLowerLevelData D,
      let Wnew := W.mapHeightPreserving K hK
      Wnew.level = W.level ∧ Wnew.label = W.label ∧ Wnew.leg = W.leg ∧
      ∀ a : Fin 2, Wnew.disc a = (W.disc a).mapDiffeomorph (F W.level)) ∧
    (∀ eta : ℝ,
      (∀ q : UnitTwoSphere, |H (psiNew (q, 0)) - c| < eta) ↔
        (∀ q : UnitTwoSphere, |H (j q) - c| < eta)) ∧
    (∀ z : ℝ, ∀ x : E2,
      F z x = pi (K (L.symm (x, z))) ∧
      (F z).symm x = pi (K.symm (L.symm (x, z)))) ∧
    ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1) ∧
    ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1) ∧
    (∀ x : E2, (L.symm (x, c) ∈ Snew ↔ x ∈ Gamma)) ∧
    (∀ x : E2, x ∉ V 3 → ∀ z : ℝ, |z - c| ≤ epsilon →
      (L.symm ((F z).symm x, z) ∈ S ↔ x ∈ Gamma)) ∧
    (∀ x : E2, x ∉ V 3 → ∀ z : ℝ, |z - c| ≤ epsilon →
      (L.symm (x, z) ∈ Snew ↔ x ∈ Gamma)) ∧
    (∀ y ∈ S, |H y - c| ≤ epsilon → pi y ∉ V 4 →
      let x := F (H y) (pi y)
      x ∉ V 3 ∧ x ∈ Gamma ∧ K y = L.symm (x, H y) ∧
      y = L.symm ((F (H y)).symm x, H y)) ∧
    Anew.source = A.source ∧ Anew.target = K '' A.target ∧
    ContDiffOn ℝ ∞ Anew Anew.source ∧ ContDiffOn ℝ ∞ Anew.symm Anew.target ∧
    (∀ w ∈ Anew.source,
      Anew w = L.symm (F w.2 (P w.1), w.2) ∧ H (Anew w) = w.2 ∧
      (Anew w ∈ Snew ↔ w.2 = c + Q w.1)) ∧
    (∀ y ∈ Anew.target,
      Anew.symm y = (P.symm ((F (H y)).symm (pi y)), H y)) ∧
    (∀ s ∈ B (r 0), ∀ z : ℝ, |z - c| ≤ 4 * b →
      Anew (s, z) = A (s, z)) ∧
    IsOpen O ∧ A6.source = U6 ∧ A6.target = Anew '' U6 ∧
    ContDiffOn ℝ ∞ A6 A6.source ∧ ContDiffOn ℝ ∞ A6.symm A6.target ∧
    L.symm '' O ⊆ A6.target ∧
    (∀ p ∈ O,
      (P.symm ((F p.2).symm p.1), p.2) ∈ U6 ∧
      Anew.symm (L.symm p) = (P.symm ((F p.2).symm p.1), p.2) ∧
      A6.symm (L.symm p) = (P.symm ((F p.2).symm p.1), p.2)) ∧
    Gamma ∩ (V 5 \ closure (V 4)) =
      P '' {s | s ∈ Do (r 5) ∧ s ∉ B (r 4) ∧ Q s = 0} ∧
    Snew ∩ (L.symm '' O) = L.symm ''
      ((Gamma ∩ (V 5 \ closure (V 4))) ×ˢ Ioo (c - epsilon) (c + epsilon)) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c : ℝ := H (j D.point)
  let S : Set E3 := range j
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let Q : ℝ × ℝ → ℝ := fun s =>
    D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
  let B : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
  let Do : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  obtain ⟨R, b, P, A, hR, hb, hPsource, hAsource, hPs, hPi, hAs, hAi,
    hPsourceMorse, hPform, hPcenter, hAcenter, hAtarget, hAform, hAinverse,
    hB, hBA, hAclosed, hcapgap, hcore, hreg⟩ :=
    exists_raw_saddle_piece_band_input psi hpsi u D
  have hreg' : ∀ q ∈ {q : UnitTwoSphere |
      |⟪(u : E3), psi (q, 0)⟫_ℝ - c| ≤ 2 * b ∧
      pi (psi (q, 0)) ∉ P '' Do (R / 4)},
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0 := by
    intro q hq
    apply hreg q
    · simpa only [j, H, c, pi, Do, InnerProductSpace.toDual_apply_apply] using hq.1
    · simpa only [j, H, c, pi, Do, InnerProductSpace.toDual_apply_apply] using hq.2
  obtain ⟨Ffield, hFfield, hSfield, KF, LF, hKF, hLF, KV, LV, hKV, hLV,
    tau, delta, epsilon, chi, hchi, hschi, I, Anew0, hFsupport, hFunit,
    hFflow, hCflow, htau, htaub, htracks, hdelta, hgap23, hgap34, hgap56,
    hepsilon, heb, het, hed, her, hmove2, hchirange, hchione, hchis,
    hI, hIsmooth, hIinverse, hIzero, hIheight, hCiso, hIsupport, hIfix,
    hclockmem, hnewmem, hreverse, hAnew0, hAnewsource0, hAnewtarget0,
    hAnewsmooth0, hAnewinverse0, hAnewgraph0, hAnewbuffer0, hAnewfixed0,
    hO0, hA6source0, hA6target0, hA6smooth0, hA6inverse0, hOtarget0,
    hOinverse0, hannulus, hproduct⟩ :=
    exists_relative_collar_band_verticalization psi hpsi u c D.morseSign1
      D.morseSign2 R b D.morseSign1_sq D.morseSigns_opposite hR hb P hPs hPi A
      hAs hAi (by simpa only [B] using hB) (by simpa only [B, c] using hBA)
      (by
        intro s hs z hz
        have hz' : z ∈ Icc (c - 4 * b) (c + 4 * b) := by
          rcases abs_le.mp hz with ⟨hzl, hzr⟩
          exact ⟨by linarith, by linarith⟩
        simpa only [L, c] using (hAform (s, z) (hBA ⟨hs, hz'⟩)).1)
      (by
        intro w hw
        simpa only [H, InnerProductSpace.toDual_apply_apply] using (hAform w hw).2.1)
      (by
        intro w hw
        simpa only [S, j, Q, c] using (hAform w hw).2.2)
      hreg'
  let r : ℕ → ℝ := fun i => (((i : ℝ) + 1) / 8) * R
  let V : ℕ → Set E2 := fun i => P '' Do (r i)
  let K := I 1
  let hK := fun y => (hIheight 1 y).1
  let psiNew : UnitTwoSphere × ℝ → E3 := fun p => K (psi p)
  let Dnew := D.mapHeightPreserving K hK
  let Snew : Set E3 := range (fun q : UnitTwoSphere => psiNew (q, 0))
  let F := heightPreservingSliceDiffeomorph u K hK
  let Gamma : Set E2 := {x | L.symm (x, c) ∈ S}
  let Anew := A.trans K.toHomeomorph.toOpenPartialHomeomorph
  let U6 : Set ((ℝ × ℝ) × ℝ) := Do (r 6) ×ˢ Ioo (c - 4 * b) (c + 4 * b)
  have hU6 : IsOpen U6 :=
    (morseRadialDisc_geometry (r 6) (by dsimp [r]; positivity)).1.prod isOpen_Ioo
  let A6 := Anew.restrOpen U6 hU6
  let O : Set (E2 × ℝ) :=
    (V 5 \ closure (V 4)) ×ˢ Ioo (c - epsilon) (c + epsilon)
  let Csupport : Set E3 :=
    L.symm '' ((Prod.snd '' tsupport (horizontalBandField u Ffield)) ×ˢ tsupport chi)
  have hrpos (i : ℕ) : 0 < r i := by
    dsimp [r]
    positivity
  have hrle (i : ℕ) (hi : i ≤ 6) : r i ≤ R := by
    have hi' : (i : ℝ) ≤ 6 := by exact_mod_cast hi
    dsimp [r]
    nlinarith
  have hrlt (i k : ℕ) (hik : i < k) : r i < r k := by
    have hik' : (i : ℝ) < k := by exact_mod_cast hik
    dsimp [r]
    exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (by linarith) (by norm_num)) hR
  obtain ⟨hgeom, hnest0⟩ := morseRadialChart_geometry P R hR
    hB
  have hgeom' (i : ℕ) (hi : i ≤ 6) : IsOpen (V i) ∧
      IsCompact (closure (V i)) ∧ closure (V i) = P '' B (r i) := by
    dsimp [V]
    exact hgeom (r i) (hrpos i) (hrle i hi)
  have hnest (i k : ℕ) (hik : i < k) (hk : k ≤ 6) :
      closure (V i) ⊆ V k := by
    dsimp [V]
    exact hnest0 (r i) (r k) (hrpos i) (hrlt i k hik) (hrle k hk)
  have hheight : ∀ s : ℝ, ∀ y : E3,
      ⟪(u : E3), I s y⟫_ℝ = ⟪(u : E3), y⟫_ℝ ∧
      ⟪(u : E3), (I s).symm y⟫_ℝ = ⟪(u : E3), y⟫_ℝ := by
    intro s y
    simpa only [H, InnerProductSpace.toDual_apply_apply] using hIheight s y
  have hCsupport : IsCompact Csupport := by
    exact hCiso
  have hCsupport_height :
      Csupport ⊆ {y : E3 | |H y - c| < 2 * epsilon} := by
    rintro y ⟨p, hp, rfl⟩
    have hz := hchis hp.2
    change |(⟪(u : E3), L.symm (p.1, p.2)⟫_ℝ) - c| < 2 * epsilon
    have hheightp : ⟪(u : E3), L.symm (p.1, p.2)⟫_ℝ = p.2 := by
      simpa only [L, heightPlaneCoordinates_snd] using
        congrArg Prod.snd (L.apply_symm_apply (p.1, p.2))
    rw [hheightp]
    exact abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hIfixcap (s : ℝ) (i : Fin D.capCount) (y : E3)
      (hy : y ∈ (D.cap i).cap) :
      I s y = y ∧ (I s).symm y = y := by
    apply hIfix s y
    right
    right
    have hgap := hcapgap i y hy
    linarith [heb]
  have hpsiNew : IsCollarEmbedding psiNew := by
    dsimp [psiNew, K]
    exact IsCollarEmbedding.postcompose_diffeomorph hpsi (I 1)
  have hpsiNew_inv (p : UnitTwoSphere × ℝ) : K.symm (psiNew p) = psi p := by
    dsimp [psiNew, K]
    exact (I 1).symm_apply_apply (psi p)
  have hpsiNew_height (p : UnitTwoSphere × ℝ) :
      H (psiNew p) = H (psi p) := by
    dsimp [psiNew, K, H]
    simpa only [InnerProductSpace.toDual_apply_apply] using (hIheight 1 (psi p)).1
  have hSnew : Snew = K '' S := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨j q, ⟨q, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩
  have hSnew_inv : K.symm '' Snew = S := by
    rw [hSnew]
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [K, Diffeomorph.symm_apply_apply] using hw
    · rintro ⟨q, rfl⟩
      exact ⟨K (j q), ⟨j q, ⟨q, rfl⟩, rfl⟩, K.symm_apply_apply _⟩
  obtain ⟨hKi, hFforward, hFinverse, hFrec, hFrecsym, hFsmooth,
    hFinvsmooth, hFdom⟩ := heightPreservingSliceDiffeomorph_geometry u K hK
  have hFforward' (z : ℝ) (x : E2) :
      F z x = pi (K (L.symm (x, z))) := by
    simpa only [F, L, pi, horizontalBandProjection_apply] using hFforward z x
  have hFinverse' (z : ℝ) (x : E2) :
      (F z).symm x = pi (K.symm (L.symm (x, z))) := by
    simpa only [F, L, pi, horizontalBandProjection_apply] using hFinverse z x
  have hFrec' (z : ℝ) (x : E2) :
      K (L.symm (x, z)) = L.symm (F z x, z) := by
    exact hFrec z x
  have hFrecsym' (z : ℝ) (x : E2) :
      K.symm (L.symm (x, z)) = L.symm ((F z).symm x, z) := by
    exact hFrecsym z x
  have hFsmooth' : ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1) := by
    exact hFsmooth
  have hFinvsmooth' : ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1) := by
    exact hFinvsmooth
  have hDgeom := SaddlePieceData.mapHeightPreserving_geometry D K hK
  have hcases := SaddlePieceData.mapHeightPreserving_cases D K hK
  have hAnew0_eq : Anew0 = Anew := by
    simpa only [Anew, K] using hAnew0
  have hAnewsource : Anew.source = A.source := by
    simpa only [hAnew0_eq] using hAnewsource0
  have hAnewtarget : Anew.target = K '' A.target := by
    simpa only [hAnew0_eq, K] using hAnewtarget0
  have hAnewsmooth : ContDiffOn ℝ ∞ Anew Anew.source := by
    simpa only [hAnew0_eq] using hAnewsmooth0
  have hAnewinverse : ContDiffOn ℝ ∞ Anew.symm Anew.target := by
    simpa only [hAnew0_eq] using hAnewinverse0
  have hA6source : A6.source = U6 := by
    simpa only [A6, hAnew0_eq] using hA6source0
  have hA6target : A6.target = Anew '' U6 := by
    simpa only [A6, hAnew0_eq] using hA6target0
  have hA6smooth : ContDiffOn ℝ ∞ A6 A6.source := by
    simpa only [A6, hAnew0_eq] using hA6smooth0
  have hA6inverse : ContDiffOn ℝ ∞ A6.symm A6.target := by
    simpa only [A6, hAnew0_eq] using hA6inverse0
  have hIsupport' (s : ℝ) :
      tsupport (fun y => I s y - y) ⊆ Csupport ∧
        tsupport (fun y => (I s).symm y - y) ⊆ Csupport := by
    simpa only [Csupport] using hIsupport s
  have hLheight (x : E2) (z : ℝ) : H (L.symm (x, z)) = z := by
    simpa only [L, H, InnerProductSpace.toDual_apply_apply,
      heightPlaneCoordinates_snd] using congrArg Prod.snd (L.apply_symm_apply (x, z))
  have hLprojection (x : E2) (z : ℝ) : pi (L.symm (x, z)) = x := by
    exact congrArg Prod.fst (L.apply_symm_apply (x, z))
  have hLreconstruct (y : E3) : L.symm (pi y, H y) = y := by
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl (by
      simp only [L, H, InnerProductSpace.toDual_apply_apply, heightPlaneCoordinates_snd])
  have hAnewformula (w : (ℝ × ℝ) × ℝ) (hw : w ∈ Anew.source) :
      Anew w = L.symm (F w.2 (P w.1), w.2) := by
    have hwA : w ∈ A.source := hAnewsource ▸ hw
    change K (A w) = _
    rw [(hAform w hwA).1, hFrec']
  have hAnewheightgraph (w : (ℝ × ℝ) × ℝ) (hw : w ∈ Anew.source) :
      H (Anew w) = w.2 ∧ (Anew w ∈ Snew ↔ w.2 = c + Q w.1) := by
    have hw0 : w ∈ Anew0.source := by simpa only [hAnew0_eq] using hw
    simpa only [hAnew0_eq, hSnew, K, S, j, Q] using
      hAnewgraph0 w hw0
  have hAnewinverse_formula (y : E3) (hy : y ∈ Anew.target) :
      Anew.symm y = (P.symm ((F (H y)).symm (pi y)), H y) := by
    have hyA : K.symm y ∈ A.target := by
      rw [hAnewtarget] at hy
      rcases hy with ⟨z, hz, rfl⟩
      simpa only [K, Diffeomorph.symm_apply_apply] using hz
    have hAinv := hAinverse (K.symm y) hyA
    have hpi : pi (K.symm y) = (F (H y)).symm (pi y) := by
      rw [hFinverse', hLreconstruct]
    have hcomp : Anew.symm y = A.symm (K.symm y) := by
      rfl
    rw [hcomp, hAinv, hpi]
    exact Prod.ext rfl (hIheight 1 y).2
  have hAnewfixed (s : ℝ × ℝ) (hs : s ∈ B (r 0)) (z : ℝ)
      (hz : |z - c| ≤ 4 * b) : Anew (s, z) = A (s, z) := by
    simpa only [hAnew0_eq] using hAnewfixed0 s hs z hz
  have hpsi_new_point : psiNew (Dnew.point, 0) = j D.point := by
    have hp := (hIfix 1 (j D.point) (Or.inr (Or.inl rfl))).1
    change K (psi (D.point, 0)) = psi (D.point, 0)
    exact hp
  have hXi (x : E2) (z : ℝ) (hz : |z - c| ≤ epsilon) :
      F z x = clockEvolution (horizontalBandField u Ffield) hKV hLV z c x ∧
      (F z).symm x = clockEvolution (horizontalBandField u Ffield) hKV hLV c z x := by
    have hi := hI 1 (L.symm (x, z))
    change K (L.symm (x, z)) = L.symm
        (clockEvolution (horizontalBandField u Ffield) hKV hLV
          (c + 1 * chi (H (L.symm (x, z))) * (H (L.symm (x, z)) - c)) c
          (pi (L.symm (x, z))), H (L.symm (x, z))) ∧
      K.symm (L.symm (x, z)) = L.symm
        (clockEvolution (horizontalBandField u Ffield) hKV hLV c
          (c + 1 * chi (H (L.symm (x, z))) * (H (L.symm (x, z)) - c))
          (pi (L.symm (x, z))), H (L.symm (x, z))) at hi
    have ht : c + 1 * chi z * (z - c) = z := by rw [hchione z hz]; ring
    rw [hLheight, hLprojection, ht, hFrec', hFrecsym'] at hi
    exact ⟨congrArg Prod.fst (L.symm.injective hi.1),
      congrArg Prod.fst (L.symm.injective hi.2)⟩
  have hcentral (x : E2) : L.symm (x, c) ∈ Snew ↔ x ∈ Gamma := by
    have hfix := hIfix 1 (L.symm (x, c)) (Or.inr (Or.inl (hLheight x c)))
    rw [hSnew]
    change L.symm (x, c) ∈ K '' S ↔ L.symm (x, c) ∈ S
    constructor
    · rintro ⟨y, hy, heq⟩
      have heq' : y = L.symm (x, c) := by
        calc
          y = K.symm (K y) := (K.symm_apply_apply y).symm
          _ = K.symm (L.symm (x, c)) := congrArg K.symm heq
          _ = L.symm (x, c) := hfix.2
      exact heq' ▸ hy
    · intro hx
      exact ⟨L.symm (x, c), hx, hfix.1⟩
  have hclockF (x : E2) (hx : x ∉ V 3) (z : ℝ) (hz : |z - c| ≤ epsilon) :
      L.symm ((F z).symm x, z) ∈ S ↔ x ∈ Gamma := by
    rw [(hXi x z hz).2]
    exact hclockmem x hx z hz
  have hnewF (x : E2) (hx : x ∉ V 3) (z : ℝ) (hz : |z - c| ≤ epsilon) :
      L.symm (x, z) ∈ Snew ↔ x ∈ Gamma := by
    rw [hSnew]
    exact hnewmem x hx z hz
  have hreverseF (y : E3) (hy : y ∈ S) (hz : |H y - c| ≤ epsilon)
      (hp : pi y ∉ V 4) :
      let x := F (H y) (pi y)
      x ∉ V 3 ∧ x ∈ Gamma ∧ K y = L.symm (x, H y) ∧
        y = L.symm ((F (H y)).symm x, H y) := by
    dsimp only
    have hr := hreverse y hy hz hp
    change clockEvolution (horizontalBandField u Ffield) hKV hLV (H y) c (pi y) ∉ V 3 ∧
      clockEvolution (horizontalBandField u Ffield) hKV hLV (H y) c (pi y) ∈ Gamma ∧
      K y = L.symm (clockEvolution (horizontalBandField u Ffield) hKV hLV
        (H y) c (pi y), H y) ∧
      y = L.symm (clockEvolution (horizontalBandField u Ffield) hKV hLV c (H y)
        (clockEvolution (horizontalBandField u Ffield) hKV hLV (H y) c (pi y)), H y) at hr
    rw [← (hXi (pi y) (H y) hz).1,
      ← (hXi (F (H y) (pi y)) (H y) hz).2] at hr
    exact hr
  have hO : IsOpen O := hO0
  have hOtarget : L.symm '' O ⊆ A6.target := by
    simpa only [A6, hAnew0_eq] using hOtarget0
  have hOinverse (p : E2 × ℝ) (hp : p ∈ O) :
      (P.symm ((F p.2).symm p.1), p.2) ∈ U6 ∧
      Anew.symm (L.symm p) = (P.symm ((F p.2).symm p.1), p.2) ∧
      A6.symm (L.symm p) = (P.symm ((F p.2).symm p.1), p.2) := by
    have hz : |p.2 - c| ≤ epsilon := by
      exact (abs_lt.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩).le
    have hinv := hOinverse0 p hp
    rw [hAnew0_eq, ← (hXi p.1 p.2 hz).2] at hinv
    exact ⟨hinv.1, hinv.2, hinv.2⟩
  have hcapfields (i : Fin D.capCount) :
      (Dnew.cap i).sourceCap = (D.cap i).sourceCap ∧
      (Dnew.cap i).sourceSeam = (D.cap i).sourceSeam ∧
      (Dnew.cap i).cap = (D.cap i).cap ∧ (Dnew.cap i).seam = (D.cap i).seam ∧
      (Dnew.cap i).tube.source = (D.cap i).tube.source ∧
      (Dnew.cap i).tube.target = K '' (D.cap i).tube.target ∧
      (∀ p : E2 × ℝ, (Dnew.cap i).tube p = K ((D.cap i).tube p)) ∧
      (∀ y : E3, (Dnew.cap i).tube.symm y = (D.cap i).tube.symm (K.symm y)) ∧
      (∀ T : Set (E2 × ℝ), (Dnew.cap i).tube '' T = K '' ((D.cap i).tube '' T)) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hforward, hinverse,
      hsource, htarget, himage, _, hsourceCap, hsourceSeam, hcap, hseam⟩ :=
      (D.cap i).mapHeightPreserving_geometry K hK
    have hfiximage (T : Set E3) (hT : T ⊆ (D.cap i).cap) : K '' T = T := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change I 1 z ∈ T
        rwa [(hIfixcap 1 i z (hT hz)).1]
      · intro hy
        exact ⟨y, hy, (hIfixcap 1 i y (hT hy)).1⟩
    change ((D.cap i).mapHeightPreserving K hK).sourceCap = _ ∧ _
    refine ⟨hsourceCap, hsourceSeam, hcap.trans (hfiximage _ subset_rfl),
      hseam.trans (hfiximage _ ?_), hsource, htarget, hforward, hinverse, himage⟩
    rw [(D.cap i).seam_eq_image, (D.cap i).cap_eq_image]
    exact image_mono (fun q hq => hq.le)
  obtain ⟨hDcount, hDcap, hDcore, hDpoint, hDlower, hDupper,
    hDmorse, hDsign1, hDsign2, hDprotected, hDcut, _⟩ := hDgeom
  refine ⟨R, b, epsilon, P, A, I, Csupport, hR, hb, hepsilon, hheight, ?_⟩
  refine ⟨heb, her, hPsource, hAsource, hPs, hPi, hAs, hAi, hPsourceMorse,
    hPform, hPcenter, hAcenter, hAtarget, hAform, hAinverse, hB, hBA, hcapgap,
    hcore, hgeom', hnest, hIsmooth, hIinverse, hIzero, hCsupport,
    hCsupport_height, hIsupport', hIfix, ?_, hpsiNew, hpsiNew_inv,
    hpsiNew_height, hSnew, hSnew_inv, hpsi_new_point, hDcount, hDcap,
    hDcore, hDpoint, hDlower, hDupper, hDmorse, hDsign1, hDsign2,
    hDprotected, hDcut, hcapfields, hIfixcap, hcases.1, hcases.2, ?_, ?_, ?_,
    hFsmooth', hFinvsmooth', hcentral, hclockF, hnewF, hreverseF,
    hAnewsource, hAnewtarget, hAnewsmooth, hAnewinverse, ?_, hAnewinverse_formula,
    hAnewfixed, hO, hA6source, hA6target, hA6smooth, hA6inverse,
    hOtarget, hOinverse, hannulus, ?_⟩
  · intro s
    exact IsCollarEmbedding.postcompose_diffeomorph hpsi (I s)
  · intro W
    have hw := W.mapHeightPreserving_geometry K hK
    exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
  · intro eta
    change (∀ q : UnitTwoSphere, |H (psiNew (q, 0)) - c| < eta) ↔
      (∀ q : UnitTwoSphere, |H (j q) - c| < eta)
    simp only [hpsiNew_height, j]
  · intro z x
    exact ⟨hFforward' z x, hFinverse' z x⟩
  · intro w hw
    exact ⟨hAnewformula w hw, hAnewheightgraph w hw⟩
  · change Snew ∩ (L.symm '' O) = L.symm ''
      ((Gamma ∩ (V 5 \ closure (V 4))) ×ˢ Ioo (c - epsilon) (c + epsilon))
    rw [hSnew]
    exact hproduct

end PoincareConjecture.M25.Topology3D
