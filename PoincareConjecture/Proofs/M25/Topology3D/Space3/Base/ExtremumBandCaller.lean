import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumRegularBand










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilySourceAtlas.exists_extremum_band
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (atlas : FamilySourceAtlas original S)
    (horiginal : IsCollarEmbedding original)
    (hgap : ∀ k : Fin r, ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) p = 0 →
      4 * D < |⟪(u : E3), original (p, 0)⟫_ℝ - cut k|)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (i : Fin n)
    (hterminal :
      (S.sourceCore i ∩ {p : UnitTwoSphere |
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p = 0}).Subsingleton)
    (q : UnitTwoSphere) (hqCore : q ∈ S.sourceCore i)
    (hqCritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hqe : q ∈ e.source) (heq : e q = 0)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ p ∈ e.source, ⟪(u : E3), psi i (p, 0)⟫_ℝ =
      ⟪(u : E3), psi i (q, 0)⟫_ℝ +
        kappa * ((e p).1 ^ 2 + (e p).2 ^ 2))
    (d : ℝ) (hd : 0 < d) :
    let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    let F : OpenPartialHomeomorph E2 UnitTwoSphere :=
      L.toHomeomorph.transOpenPartialHomeomorph e.symm
    let j : UnitTwoSphere → E3 := fun p => psi i (p, 0)
    let c : ℝ := ⟪(u : E3), j q⟫_ℝ
    let W : Set E3 :=
      {y | ∀ k : Fin r, 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|}
    let U : Set UnitTwoSphere := (atlas.chart i).source ∩ j ⁻¹' W
    F.source = L ⁻¹' e.target ∧ F.target = e.source ∧ F 0 = q ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ F.symm F.target ∧
      IsOpen W ∧ IsOpen U ∧ q ∈ U ∧ U ⊆ S.sourceCore i ∧
      (∀ b : Fin S.capCount, Disjoint W (S.cap b).cap) ∧
      ∃ rho : ℝ, 0 < rho ∧ rho < d ∧ 2 * rho ^ 2 < D ∧
        closedBall (0 : E2) (2 * rho) ⊆ F.source ∧
        F '' closedBall (0 : E2) (2 * rho) ⊆ U ∧
        ∃ A : OpenPartialHomeomorph (E2 × ℝ) E3,
          (0, c) ∈ A.source ∧ A (0, c) = j q ∧
          ContDiffOn ℝ ∞ A A.source ∧
          ContDiffOn ℝ ∞ A.symm A.target ∧ A.target ⊆ W ∧
          closedBall (0 : E2) (2 * rho) ×ˢ
            Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source ∧
          (∀ p ∈ A.source,
            L p.1 ∈ e.target ∧ F p.1 ∈ U ∧
            A p = (heightPlaneCoordinates u).symm
              ((heightPlaneCoordinates u (j (F p.1))).1, p.2) ∧
            ⟪(u : E3), A p⟫_ℝ = p.2 ∧
            (A p ∈ range j ↔ p.2 = c + kappa * ‖p.1‖ ^ 2)) ∧
          (∀ x ∈ closedBall (0 : E2) (2 * rho),
            A (x, c + kappa * ‖x‖ ^ 2) = j (F x) ∧
            j (F x) ∈ A.target ∧
            A.symm (j (F x)) = (x, c + kappa * ‖x‖ ^ 2) ∧
            ⟪(u : E3), j (F x)⟫_ℝ = c + kappa * ‖x‖ ^ 2) ∧
          let nativeDisc : Set UnitTwoSphere := F '' closedBall (0 : E2) rho
          let nativeOpen : Set UnitTwoSphere := F '' ball (0 : E2) rho
          let nativeSeam : Set UnitTwoSphere := F '' sphere (0 : E2) rho
          let nativeRest : Set UnitTwoSphere := S.sourceCore i \ nativeOpen
          let disc : Set E3 := j '' nativeDisc
          let discOpen : Set E3 := j '' nativeOpen
          let seam : Set E3 := j '' nativeSeam
          let rest : Set E3 := S.retainedCore i \ discOpen
          let morse : E2 → E3 := fun x => A (x, c + kappa * ‖x‖ ^ 2)
          let s : ℝ := c + kappa * rho ^ 2
          q ∈ nativeOpen ∧ IsOpen nativeOpen ∧
            IsCompact nativeDisc ∧ IsCompact nativeSeam ∧
            IsConnected nativeSeam ∧
            closure nativeOpen = nativeDisc ∧
            nativeDisc \ nativeOpen = nativeSeam ∧
            frontier nativeOpen = nativeSeam ∧
            nativeDisc ⊆ S.sourceCore i ∧
            IsCompact disc ∧ IsCompact seam ∧ IsConnected seam ∧
            disc ⊆ A.target ∧
            (∀ b : Fin S.capCount, Disjoint disc (S.cap b).cap) ∧
            disc \ discOpen = seam ∧
            disc = morse '' closedBall (0 : E2) rho ∧
            discOpen = morse '' ball (0 : E2) rho ∧
            seam = morse '' sphere (0 : E2) rho ∧
            (∀ p ∈ nativeSeam, ⟪(u : E3), j p⟫_ℝ = s) ∧
            (∀ p ∈ nativeOpen \ {q},
              0 < kappa * (⟪(u : E3), j p⟫_ℝ - c) ∧
                kappa * (⟪(u : E3), j p⟫_ℝ - c) < rho ^ 2) ∧
            ∃ a : Fin S.capCount,
              S.owner a = i ∧ (S.cap a).sign = -kappa ∧
              (∀ b : Fin S.capCount, S.owner b = i ↔ b = a) ∧
              Fintype.card {b : Fin S.capCount // S.owner b = i} = 1 ∧
              let t : ℝ := (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
              let ell : ℝ := min s t
              let upper : ℝ := max s t
              ell < upper ∧
              (kappa = 1 → ell = s ∧ upper = t) ∧
              (kappa = -1 → ell = t ∧ upper = s) ∧
              rest = j '' nativeRest ∧ IsCompact rest ∧ IsConnected rest ∧
              (∀ p ∈ nativeRest,
                mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
                  (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p ≠ 0) ∧
              rest = {y : E3 | y ∈ range j ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} ∧
              (∀ p : UnitTwoSphere, j p ∈ rest →
                mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
                  (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p ≠ 0) ∧
              collarHeightLevel (psi i) (u : E3) s = seam ∧
              collarHeightLevel (psi i) (u : E3) t = (S.cap a).seam ∧
              range j = (rest ∪ disc) ∪ (S.cap a).cap ∧
              rest ∩ disc = seam ∧
              rest ∩ (S.cap a).cap = (S.cap a).seam ∧
              range j \ discOpen = rest ∪ (S.cap a).cap ∧
              ∃ eta : ℝ, 0 < eta ∧ ∃ gamma : ℝ → UnitCircle → E2,
                ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
                  (fun p : ℝ × UnitCircle => gamma p.1 p.2) ∧
                (∀ z ∈ Icc (ell - eta) (upper + eta),
                  IsPlanarEmbedding (gamma z)) ∧
                ∀ z ∈ Icc (ell - eta) (upper + eta),
                  range (gamma z) = {x : E2 |
                    (heightPlaneCoordinates u).symm (x, z) ∈ range j} := by
  classical
  let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let F : OpenPartialHomeomorph E2 UnitTwoSphere :=
    L.toHomeomorph.transOpenPartialHomeomorph e.symm
  let j : UnitTwoSphere → E3 := fun p => psi i (p, 0)
  let c : ℝ := ⟪(u : E3), j q⟫_ℝ
  let d0 := min d (min 1 (D / 2))
  have hd0 : 0 < d0 := lt_min hd
    (lt_min zero_lt_one (div_pos S.buffer_pos (by norm_num)))
  obtain ⟨hFs, hFt, hFzero, hFsmooth, hFinverse, hU, hqU, hUcore,
      rho, hrho, hrbound, hFsource, hFbuffer, A, hA0, hAq, hAs, hAi,
      hAt, hAsource, hAform, hAgraph, hgeometry⟩ :=
    atlas.exists_extremum_core_disc horiginal hgap i q hqCore hqCritical
      e hqe heq he hei kappa hkappa hform d0 hd0
  have hrd : rho < d := hrbound.trans_le (min_le_left _ _)
  have hr1 : rho < 1 :=
    hrbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrD : rho < D / 2 :=
    hrbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 2 * rho ^ 2 < D := by nlinarith only [hrho, hr1, hrD]
  obtain ⟨hW, _hU, _hqU, _hUcore, hWavoid⟩ :=
    atlas.critical_protected_neighborhood horiginal hgap i q hqCore hqCritical
  obtain ⟨hqOpen, hOpen, hNativeCompact, hNativeSeamCompact, hNativeSeamConnected,
      hClosure, hNativeDiff, hFrontier, hDiscCore, hDiscCompact, hSeamCompact,
      hSeamConnected, hDiscTarget, hAvoid, hDiscDiff, hSeamHeight, hBounds⟩ := hgeometry
  have hqSource : q ∈ (atlas.chart i).source := atlas.core_subset_source i hqCore
  have hOriginalCritical := (atlas.height_critical_iff horiginal i q hqSource).mp hqCritical
  have hcentral : psi i (q, 0) = original (atlas.chart i q, 0) := by
    simpa only [mul_zero] using atlas.collar_eq i q hqSource 0 (by norm_num)
  have hCurrentGap (k : Fin r) :
      4 * D < |⟪(u : E3), psi i (q, 0)⟫_ℝ - cut k| := by
    rw [hcentral]
    exact hgap k (atlas.chart i q) hOriginalCritical
  obtain ⟨hLower, hUpper⟩ :=
    S.seam_height_gaps_of_buffer_avoidance hzero i q hCurrentGap
  have hUnique (p : UnitTwoSphere) (hp : p ∈ S.sourceCore i)
      (hc : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p = 0) : p = F 0 :=
    (hterminal ⟨hp, hc⟩ ⟨hqCore, hqCritical⟩).trans hFzero.symm
  have hBufferCore : F '' closedBall (0 : E2) (2 * rho) ⊆ S.sourceCore i :=
    hFbuffer.trans hUcore
  have hHeight (x : E2) (hx : x ∈ closedBall (0 : E2) (2 * rho)) :
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2 :=
    (hAgraph x hx).2.2.2
  obtain ⟨a, ha, hSign, hOwner, hCard, hOrder, hPositive, hNegative, hImage,
      hCompact, hConnected, hNativeRegular, hBand, hRegular, hNewLevel, hOldLevel,
      eta, heta, gamma, hGamma, hEmbedding, hLevels⟩ :=
    S.exists_morse_rest_circle_family i F rho hrho hsmall hFsource hBufferCore hAvoid
      c kappa hkappa hHeight hUnique hLower hUpper
  let nativeRest := S.sourceCore i \ (F '' ball (0 : E2) rho)
  let disc := j '' (F '' closedBall (0 : E2) rho)
  let discOpen := j '' (F '' ball (0 : E2) rho)
  let seam := j '' (F '' sphere (0 : E2) rho)
  let rest := S.retainedCore i \ discOpen
  let morse := fun x : E2 => A (x, c + kappa * ‖x‖ ^ 2)
  have hRadius : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  have hImages (K : Set E2) (hK : K ⊆ closedBall (0 : E2) (2 * rho)) :
      j '' (F '' K) = morse '' K := by
    rw [image_image]
    exact image_congr fun x hx => (hAgraph x (hK hx)).1.symm
  have hDiscImage : disc = morse '' closedBall (0 : E2) rho := hImages _ hRadius
  have hOpenImage : discOpen = morse '' ball (0 : E2) rho :=
    hImages _ (ball_subset_closedBall.trans hRadius)
  have hSeamImage : seam = morse '' sphere (0 : E2) rho :=
    hImages _ (sphere_subset_closedBall.trans hRadius)
  obtain ⟨_hRc, _hRn, _hNot, _hReg, _hNative, hRestImage, _hLc, _hLn,
      hCover, hNew, hOld, _hDisjoint⟩ :=
    S.morse_disc_complement_geometry i F rho hrho (hRadius.trans hFsource)
      hDiscCore hAvoid hUnique
  change j '' nativeRest = rest at hRestImage
  have hOwned : (⋃ b : {b : Fin S.capCount // S.owner b = i}, (S.cap b.1).cap) =
      (S.cap a).cap := by
    ext y
    constructor
    · intro hy
      obtain ⟨b, hb⟩ := mem_iUnion.mp hy
      exact (hOwner b.1).mp b.2 ▸ hb
    · intro hy
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, hy⟩
  change range j = ((j '' nativeRest) ∪ disc) ∪
    (⋃ b : {b : Fin S.capCount // S.owner b = i}, (S.cap b.1).cap) at hCover
  rw [hRestImage, hOwned] at hCover
  change (j '' nativeRest) ∩ disc = seam at hNew
  rw [hRestImage] at hNew
  have hRestCap := hOld a ha
  change (j '' nativeRest) ∩ (S.cap a).cap = (S.cap a).seam at hRestCap
  rw [hRestImage] at hRestCap
  have hOpenDisc : discOpen ⊆ disc := image_mono (image_mono ball_subset_closedBall)
  have hWholeDiff : range j \ discOpen = rest ∪ (S.cap a).cap := by
    ext y
    constructor
    · rintro ⟨hy, hyOpen⟩
      rw [hCover] at hy
      rcases hy with (hy | hy) | hy
      · exact Or.inl hy
      · exact Or.inl ((hNew.ge (hDiscDiff.le ⟨hy, hyOpen⟩)).1)
      · exact Or.inr hy
    · rintro (hy | hy)
      · exact ⟨hCover.ge (Or.inl (Or.inl hy)), hy.2⟩
      · refine ⟨hCover.ge (Or.inr hy), ?_⟩
        intro hOpenY
        exact disjoint_left.mp (hAvoid a) (hOpenDisc hOpenY) hy
  refine ⟨hFs, hFt, hFzero, hFsmooth, hFinverse, hW, hU, hqU, hUcore, hWavoid,
    rho, hrho, hrd, hsmall, hFsource, hFbuffer, A, hA0, hAq, hAs, hAi,
    hAt, hAsource, hAform, hAgraph, ?_⟩
  exact ⟨hqOpen, hOpen, hNativeCompact, hNativeSeamCompact, hNativeSeamConnected,
    hClosure, hNativeDiff, hFrontier, hDiscCore, hDiscCompact, hSeamCompact,
    hSeamConnected, hDiscTarget, hAvoid, hDiscDiff, hDiscImage, hOpenImage,
    hSeamImage, hSeamHeight, hBounds, a, ha, hSign, hOwner, hCard, hOrder,
    hPositive, hNegative, hImage, hCompact, hConnected, hNativeRegular,
    hBand, hRegular, hNewLevel, hOldLevel, hCover, hNew, hRestCap, hWholeDiff,
    eta, heta, gamma, hGamma, hEmbedding, hLevels⟩

end PoincareConjecture.M25.Topology3D
