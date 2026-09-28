import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceScalarWindow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceCutConjugacy

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology Matrix

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_reference_three_cut_relocation
    (ws wm d alpha beta nu t z v : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32)) :
    let U : E2 → ℝ := fun x =>
      ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
    let k : ℝ := U !₂[-Real.sqrt (1 - ws ^ 2), 0]
    let mu : ℝ := U !₂[Real.sqrt (1 - wm ^ 2), 0]
    ((17 : ℝ) / 16 < alpha ∧ alpha < beta ∧ beta < k) →
    ((17 : ℝ) / 16 < t ∧ t < z ∧ z < k) →
    (k < nu ∧ nu < mu) → (k < v ∧ v < mu) →
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let B : BallNeighborhoodChart E3 E3 := nestedReferenceBallChart d
    let S : Set E3 := B.boundary
    ∃ (eO eI eU sigma : ℝ)
      (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (K : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (C : Set ℝ),
      0 < eO ∧ 0 < eI ∧ 0 < eU ∧ 0 < sigma ∧
      IsCompact C ∧
      C ⊆ Ioo (17 / 16 + d) (k + d) ∪ Ioo (k + d) (mu + d) ∧
      Disjoint (Icc (k + d - sigma) (k + d + sigma)) C ∧
      StrictMono g ∧ StrictMono g.symm ∧
      (∀ x : ℝ, x ∉ C → g x = x ∧ g.symm x = x) ∧
      (∀ y : E3, H0 y ∉ C → K y = y ∧ K.symm y = y) ∧
      (∀ y : E3, H0 (K y) = g (H0 y) ∧
        H0 (K.symm y) = g.symm (H0 y)) ∧
      (∀ y : E3, (K y ∈ S ↔ y ∈ S) ∧ (K.symm y ∈ S ↔ y ∈ S)) ∧
      K '' S = S ∧ K.symm '' S = S ∧
      K '' B.inside = B.inside ∧ K.symm '' B.inside = B.inside ∧
      K '' B.closedRegion = B.closedRegion ∧
      K.symm '' B.closedRegion = B.closedRegion ∧
      (∀ h : ℝ, |h| ≤ eO →
        g (d + alpha + h) = d + t + h ∧
        g.symm (d + t + h) = d + alpha + h) ∧
      (∀ h : ℝ, |h| ≤ eI →
        g (d + beta + h) = d + z + h ∧
        g.symm (d + z + h) = d + beta + h) ∧
      (∀ h : ℝ, |h| ≤ eU →
        g (d + nu + h) = d + v + h ∧
        g.symm (d + v + h) = d + nu + h) ∧
      ∀ Q : Set ℝ,
        K '' (S ∩ H0 ⁻¹' Q) = S ∩ H0 ⁻¹' (g '' Q) ∧
        K.symm '' (S ∩ H0 ⁻¹' (g '' Q)) = S ∩ H0 ⁻¹' Q := by
  classical
  let U : E2 → ℝ := fun x =>
    ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
  let k : ℝ := U !₂[-Real.sqrt (1 - ws ^ 2), 0]
  let mu : ℝ := U !₂[Real.sqrt (1 - wm ^ 2), 0]
  intro _ _ _ hOld hNew hNu hV
  let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
  let B : BallNeighborhoodChart E3 E3 := nestedReferenceBallChart d
  let S : Set E3 := B.boundary
  change 17 / 16 < alpha ∧ alpha < beta ∧ beta < k at hOld
  change 17 / 16 < t ∧ t < z ∧ z < k at hNew
  change k < nu ∧ nu < mu at hNu
  change k < v ∧ v < mu at hV
  change ∃ (eO eI eU sigma : ℝ)
    (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (K : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C : Set ℝ), _
  obtain ⟨_hSmooth, _hklo, _hkhi, _hmulo, _hqs, _hqm, _hks, _hmum,
    _hclass, _hreg, hRegular⟩ :=
    reference_high_sphere_regularity ws wm d hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  let psi : UnitTwoSphere × ℝ → E3 := fun p =>
    nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
  obtain ⟨hpsi, hSurface, _⟩ := exists_nestedReference_collar d
  change IsCollarEmbedding psi at hpsi
  change range (fun q : UnitTwoSphere => psi (q, 0)) = S at hSurface
  let u0 : UnitTwoSphere := ⟨heightCoordinates.symm ((0 : E2), (1 : ℝ)), by
    rw [mem_sphere_zero_iff_norm]
    have hh := heightCoordinates_symm_norm_sq ((0 : E2), (1 : ℝ))
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), one_pow, zero_add] at hh
    nlinarith [norm_nonneg (heightCoordinates.symm ((0 : E2), (1 : ℝ)))]⟩
  have hu (y : E3) : ⟪(u0 : E3), y⟫_ℝ = H0 y := by
    change ⟪heightCoordinates.symm ((0 : E2), (1 : ℝ)), y⟫_ℝ = _
    simp [heightCoordinates_symm_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three, H0]
  let L := heightPlaneCoordinates u0
  have hLH (y : E3) : (L y).2 = H0 y :=
    (heightPlaneCoordinates_snd u0 y).trans (hu y)
  have hNative : (fun q : UnitTwoSphere => ⟪(u0 : E3), psi (q, 0)⟫_ℝ) =
      (fun q : UnitTwoSphere => H0 (nestedReferenceDiffeomorph d (q : E3))) := by
    funext q
    rw [hu]
    simp only [psi, add_zero, one_smul]
  let D1 := Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
  let D3 := Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞
  let Pack : D1 → D3 → Set ℝ → Prop := fun g K C =>
    IsCompact C ∧ StrictMono g ∧ StrictMono g.symm ∧
    (∀ x : ℝ, x ∉ C → g x = x ∧ g.symm x = x) ∧
    (∀ y : E3, H0 y ∉ C → K y = y ∧ K.symm y = y) ∧
    (∀ y : E3, H0 (K y) = g (H0 y) ∧ H0 (K.symm y) = g.symm (H0 y)) ∧
    ∀ y : E3, (K y ∈ S ↔ y ∈ S) ∧ (K.symm y ∈ S ↔ y ∈ S)
  have hCompose (g1 g2 : D1) (K1 K2 : D3) (C1 C2 : Set ℝ)
      (h1 : Pack g1 K1 C1) (h2 : Pack g2 K2 C2) :
      Pack (g1.trans g2) (K1.trans K2) (C1 ∪ C2) := by
    obtain ⟨hc1, hm1, hmi1, hf1, hKf1, hH1, hS1⟩ := h1
    obtain ⟨hc2, hm2, hmi2, hf2, hKf2, hH2, hS2⟩ := h2
    refine ⟨hc1.union hc2, hm2.comp hm1, hmi1.comp hmi2, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have h1x := hf1 x (fun h => hx (Or.inl h))
      have h2x := hf2 x (fun h => hx (Or.inr h))
      change g2 (g1 x) = x ∧ g1.symm (g2.symm x) = x
      rw [h1x.1, h2x.1, h2x.2, h1x.2]
      exact ⟨rfl, rfl⟩
    · intro y hy
      have h1y := hKf1 y (fun h => hy (Or.inl h))
      have h2y := hKf2 y (fun h => hy (Or.inr h))
      change K2 (K1 y) = y ∧ K1.symm (K2.symm y) = y
      rw [h1y.1, h2y.1, h2y.2, h1y.2]
      exact ⟨rfl, rfl⟩
    · intro y
      change H0 (K2 (K1 y)) = g2 (g1 (H0 y)) ∧
        H0 (K1.symm (K2.symm y)) = g1.symm (g2.symm (H0 y))
      rw [(hH2 (K1 y)).1, (hH1 y).1, (hH1 (K2.symm y)).2, (hH2 y).2]
      exact ⟨rfl, rfl⟩
    · intro y
      exact ⟨(hS2 (K1 y)).1.trans (hS1 y).1,
        (hS1 (K2.symm y)).2.trans (hS2 y).2⟩

  have hMove (lo hi x y : ℝ)
      (hComponent : (17 / 16 ≤ lo ∧ hi ≤ k) ∨ (k ≤ lo ∧ hi ≤ mu))
      (hx : x ∈ Ioo lo hi) (hy : y ∈ Ioo lo hi) :
      ∃ (e : ℝ) (g : D1) (K : D3) (C : Set ℝ),
        0 < e ∧ Pack g K C ∧ C ⊆ Ioo (d + lo) (d + hi) ∧
        (∀ h : ℝ, |h| ≤ e → g (d + x + h) = d + y + h) ∧
        (∀ h : ℝ, |h| ≤ e →
          g (d + lo + h) = d + lo + h ∧ g (d + hi + h) = d + hi + h) ∧
        ∀ h : ℝ, |h| ≤ e →
          d + x + h ∈ Ioo (d + lo) (d + hi) ∧
          d + y + h ∈ Ioo (d + lo) (d + hi) := by
    let a := min (d + x) (d + y)
    let b := max (d + x) (d + y)
    let m := (a + b) / 2
    have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
    have hMin : a = min x y + d := by dsimp [a]; simp [min_add_add_left, add_comm]
    have hMax : b = max x y + d := by dsimp [b]; simp [max_add_add_left, add_comm]
    have hComp : (17 / 16 < min x y ∧ max x y < k) ∨
        (k < min x y ∧ max x y < mu) := by
      rcases hComponent with h | h
      · exact Or.inl ⟨h.1.trans_lt (lt_min hx.1 hy.1),
          (max_lt hx.2 hy.2).trans_le h.2⟩
      · exact Or.inr ⟨h.1.trans_lt (lt_min hx.1 hy.1),
          (max_lt hx.2 hy.2).trans_le h.2⟩
    have hReg (q : UnitTwoSphere) (hq : ⟪(u0 : E3), psi (q, 0)⟫_ℝ ∈ Icc a b) :
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u0 : E3), psi (p, 0)⟫_ℝ) q ≠ 0 := by
      change (fun p : UnitTwoSphere => ⟪(u0 : E3), psi (p, 0)⟫_ℝ) q ∈ _ at hq
      rw [hNative, hMin, hMax] at hq
      rw [hNative]
      exact hRegular (min x y) (max x y) hComp q hq
    obtain ⟨eta, _heta, hSpan, Phi, hPhi, hPhii, _hPhi0, _hPhic, hBand⟩ :=
      exists_regular_collar_horizontal_transport psi hpsi u0 a b hab hReg
    obtain ⟨e, g, C, he, hBuffer, hC, hCW, hg, hgi, _hgneg, hg0, hMono,
      _hgSupport, hFixC, hFixW, _hFixJ, _hgW, _hTrack, hAffine⟩ :=
      reference_scalar_window (d + lo) (d + hi) (d + x) (d + y) m eta
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith [hy.1], by linarith [hy.2]⟩ hSpan
    let W := Ioo (a - 3 * e) (b + 3 * e)
    have hBuffer' : Icc (a - 4 * e) (b + 4 * e) ⊆
        Ioo (d + lo) (d + hi) ∩ Ioo (m - eta) (m + eta) := hBuffer
    have hWbuffer : W ⊆ Icc (a - 4 * e) (b + 4 * e) := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hCsub : C ⊆ Ioo (d + lo) (d + hi) :=
      fun _ hs => (hBuffer' (hWbuffer (hCW hs))).1
    have hBand' (s : ℝ) (hs : s ∈ W) (p : E2) :
        L.symm (Phi s p, s) ∈ S ↔ L.symm (p, m) ∈ S := by
      simpa only [hSurface] using hBand s (hBuffer' (hWbuffer hs)).2 p
    obtain ⟨K, _hK, _hKi, hFormula, _hInvFormula, hHeight, hMem,
      hMemInv, _hImages, _hFix, _hZero⟩ :=
      reference_cut_conjugacy u0 S W m Phi hPhi hPhii hBand' g hg hgi hg0
        (fun r s hs => (hFixW r s hs).1)
    have hHeight' (s : E3) : H0 (K 1 s) = g 1 (H0 s) := by
      simpa only [hu] using hHeight 1 s
    have hKfixed (s : E3) (hs : H0 s ∉ C) :
        K 1 s = s ∧ (K 1).symm s = s := by
      have hf : g 1 (L s).2 = (L s).2 := by
        simpa only [hLH] using (hFixC 1 (H0 s) hs).1
      have hforward : K 1 s = s := by
        rw [hFormula]
        change L.symm (Phi (g 1 (L s).2) ((Phi (L s).2).symm (L s).1),
          g 1 (L s).2) = s
        rw [hf, (Phi (L s).2).apply_symm_apply, Prod.eta, L.symm_apply_apply]
      refine ⟨hforward, ?_⟩
      simpa only [(K 1).symm_apply_apply] using
        (congrArg (K 1).symm hforward).symm
    have hPack : Pack (g 1) (K 1) C := by
      refine ⟨hC, (hMono 1).1, (hMono 1).2, hFixC 1, hKfixed, ?_, ?_⟩
      · intro s
        refine ⟨hHeight' s, ?_⟩
        simpa only [(K 1).apply_symm_apply, (g 1).symm_apply_apply] using
          (congrArg (g 1).symm (hHeight' ((K 1).symm s))).symm
      · exact fun s => ⟨hMem 1 s, hMemInv 1 s⟩
    have hLeft : d + lo < a - 4 * e :=
      (hBuffer' ⟨le_rfl, by linarith⟩).1.1
    have hRight : b + 4 * e < d + hi :=
      (hBuffer' ⟨by linarith, le_rfl⟩).1.2
    refine ⟨e, g 1, K 1, C, he, hPack, hCsub,
      fun h hh => (hAffine h hh).1, ?_, ?_⟩
    · intro h hh
      have hh' := abs_le.mp hh
      constructor
      · apply (hFixW 1 (d + lo + h) _).1
        intro hmem
        have hl : a - 3 * e < d + lo + h := hmem.1
        linarith [hh'.2]
      · apply (hFixW 1 (d + hi + h) _).1
        intro hmem
        have hr : d + hi + h < b + 3 * e := hmem.2
        linarith [hh'.1]
    · intro h hh
      have hh' := abs_le.mp hh
      have hax : a ≤ d + x := min_le_left _ _
      have hay : a ≤ d + y := min_le_right _ _
      have hxb : d + x ≤ b := le_max_left _ _
      have hyb : d + y ≤ b := le_max_right _ _
      exact ⟨⟨by linarith [hh'.1], by linarith [hh'.2]⟩,
        ⟨by linarith [hh'.1], by linarith [hh'.2]⟩⟩
  have hLower : ∃ (e : ℝ) (g : D1) (K : D3) (C : Set ℝ),
      0 < e ∧ Pack g K C ∧ C ⊆ Ioo (d + 17 / 16) (d + k) ∧
      (∀ h : ℝ, |h| ≤ e →
        g (d + alpha + h) = d + t + h ∧ g (d + beta + h) = d + z + h) ∧
      ∀ h : ℝ, |h| ≤ e → d + t + h < d + k ∧ d + z + h < d + k := by
    by_cases ht : t < beta
    · obtain ⟨e1, g1, K1, C1, he1, hp1, hc1, ha1, hf1, hw1⟩ :=
        hMove (17 / 16) beta alpha t (Or.inl ⟨le_rfl, hOld.2.2.le⟩)
          ⟨hOld.1, hOld.2.1⟩ ⟨hNew.1, ht⟩
      obtain ⟨e2, g2, K2, C2, he2, hp2, hc2, ha2, hf2, hw2⟩ :=
        hMove t k beta z (Or.inl ⟨hNew.1.le, le_rfl⟩)
          ⟨ht, hOld.2.2⟩ ⟨hNew.2.1, hNew.2.2⟩
      refine ⟨min e1 e2, g1.trans g2, K1.trans K2, C1 ∪ C2,
        lt_min he1 he2, hCompose _ _ _ _ _ _ hp1 hp2, ?_, ?_, ?_⟩
      · rintro s (hs | hs)
        · exact ⟨(hc1 hs).1, (hc1 hs).2.trans (by linarith [hOld.2.2])⟩
        · exact ⟨(by linarith [hNew.1] : d + 17 / 16 < d + t).trans
            (hc2 hs).1, (hc2 hs).2⟩
      · intro h hh
        have hh1 := hh.trans (min_le_left e1 e2)
        have hh2 := hh.trans (min_le_right e1 e2)
        change g2 (g1 (d + alpha + h)) = _ ∧ g2 (g1 (d + beta + h)) = _
        rw [ha1 h hh1, (hf2 h hh2).1, (hf1 h hh1).2, ha2 h hh2]
        exact ⟨rfl, rfl⟩
      · intro h hh
        have h1 := (hw1 h (hh.trans (min_le_left e1 e2))).2.2
        have h2 := (hw2 h (hh.trans (min_le_right e1 e2))).2.2
        exact ⟨by linarith [hOld.2.2], h2⟩
    · have hbt : beta ≤ t := le_of_not_gt ht
      obtain ⟨e1, g1, K1, C1, he1, hp1, hc1, ha1, hf1, hw1⟩ :=
        hMove alpha k beta z (Or.inl ⟨hOld.1.le, le_rfl⟩)
          ⟨hOld.2.1, hOld.2.2⟩ ⟨by linarith [hOld.2.1, hNew.2.1], hNew.2.2⟩
      obtain ⟨e2, g2, K2, C2, he2, hp2, hc2, ha2, hf2, hw2⟩ :=
        hMove (17 / 16) z alpha t (Or.inl ⟨le_rfl, hNew.2.2.le⟩)
          ⟨hOld.1, by linarith [hOld.2.1, hNew.2.1]⟩ ⟨hNew.1, hNew.2.1⟩
      refine ⟨min e1 e2, g1.trans g2, K1.trans K2, C1 ∪ C2,
        lt_min he1 he2, hCompose _ _ _ _ _ _ hp1 hp2, ?_, ?_, ?_⟩
      · rintro s (hs | hs)
        · exact ⟨(by linarith [hOld.1] : d + 17 / 16 < d + alpha).trans
            (hc1 hs).1, (hc1 hs).2⟩
        · exact ⟨(hc2 hs).1, (hc2 hs).2.trans (by linarith [hNew.2.2])⟩
      · intro h hh
        have hh1 := hh.trans (min_le_left e1 e2)
        have hh2 := hh.trans (min_le_right e1 e2)
        change g2 (g1 (d + alpha + h)) = _ ∧ g2 (g1 (d + beta + h)) = _
        rw [(hf1 h hh1).1, ha2 h hh2, ha1 h hh1, (hf2 h hh2).2]
        exact ⟨rfl, rfl⟩
      · intro h hh
        have h1 := (hw1 h (hh.trans (min_le_left e1 e2))).2.2
        have h2 := (hw2 h (hh.trans (min_le_right e1 e2))).2.2
        exact ⟨by linarith [hNew.2.2], h1⟩
  obtain ⟨eL, gL, KL, CL, heL, hpL, hcL, haL, hwL⟩ := hLower
  obtain ⟨eU, gU, KU, CU, heU, hpU, hcU, haU, _hfU, hwU⟩ :=
    hMove k mu nu v (Or.inr ⟨le_rfl, le_rfl⟩) hNu hV
  let g := gL.trans gU
  let K := KL.trans KU
  let C := CL ∪ CU
  have hFinal : Pack g K C := hCompose _ _ _ _ _ _ hpL hpU
  obtain ⟨hC, hMono, hMonoi, hFixed, hKfixed, hHeight, hMem⟩ := hFinal
  have hCsub : C ⊆ Ioo (17 / 16 + d) (k + d) ∪ Ioo (k + d) (mu + d) := by
    rintro s (hs | hs)
    · exact Or.inl (by simpa only [add_comm] using hcL hs)
    · exact Or.inr (by simpa only [add_comm] using hcU hs)
  have hknot : k + d ∉ C := by
    intro h
    rcases hCsub h with h | h
    · exact lt_irrefl _ h.2
    · exact lt_irrefl _ h.1
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp hC.isClosed.isOpen_compl (k + d) hknot
  let sigma := r / 2
  have hsigma : 0 < sigma := half_pos hr
  have hDisjoint : Disjoint (Icc (k + d - sigma) (k + d + sigma)) C := by
    apply Set.disjoint_left.mpr
    intro s hs hsc
    apply hBall ?_ hsc
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [sigma] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hAffLower (h : ℝ) (hh : |h| ≤ eL) :
      g (d + alpha + h) = d + t + h ∧ g (d + beta + h) = d + z + h := by
    obtain ⟨_, _, _, hfU, _⟩ := hpU
    have htC : d + t + h ∉ CU := fun hs =>
      (not_lt_of_ge (hwL h hh).1.le) (hcU hs).1
    have hzC : d + z + h ∉ CU := fun hs =>
      (not_lt_of_ge (hwL h hh).2.le) (hcU hs).1
    change gU (gL (d + alpha + h)) = _ ∧ gU (gL (d + beta + h)) = _
    rw [(haL h hh).1, (haL h hh).2, (hfU _ htC).1, (hfU _ hzC).1]
    exact ⟨rfl, rfl⟩
  have hAffUpper (h : ℝ) (hh : |h| ≤ eU) : g (d + nu + h) = d + v + h := by
    obtain ⟨_, _, _, hfL, _⟩ := hpL
    have hnuC : d + nu + h ∉ CL := fun hs =>
      (not_lt_of_ge (hwU h hh).1.1.le) (hcL hs).2
    change gU (gL (d + nu + h)) = _
    rw [(hfL _ hnuC).1]
    exact haU h hh
  have hInverse (a b : ℝ) (hab : g a = b) : g.symm b = a := by
    rw [← hab, g.symm_apply_apply]
  have hImage : K '' S = S := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hMem x).1.mpr hx
    · intro y hy
      exact ⟨K.symm y, (hMem y).2.mpr hy, K.apply_symm_apply y⟩
  have hImageInv : K.symm '' S = S := by
    conv_lhs => rw [← hImage]
    exact K.symm_image_image S
  have hdim : 1 < Module.rank ℝ E3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E3]
  have hBoundary : (B.mapDiffeomorph K).boundary = B.boundary := by
    rw [B.mapDiffeomorph_boundary]
    exact hImage
  have hInside : K '' B.inside = B.inside := by
    rw [← B.mapDiffeomorph_inside]
    exact (B.mapDiffeomorph K).inside_eq_of_boundary_eq B hdim hBoundary
  have hClosed : K '' B.closedRegion = B.closedRegion := by
    rw [← B.mapDiffeomorph_closedRegion]
    exact (B.mapDiffeomorph K).closedRegion_eq_of_boundary_eq B hdim hBoundary
  have hInsideInv : K.symm '' B.inside = B.inside := by
    conv_lhs => rw [← hInside]
    exact K.symm_image_image B.inside
  have hClosedInv : K.symm '' B.closedRegion = B.closedRegion := by
    conv_lhs => rw [← hClosed]
    exact K.symm_image_image B.closedRegion
  refine ⟨eL, eL, eU, sigma, g, K, C, heL, heL, heU, hsigma,
    hC, hCsub, hDisjoint, hMono, hMonoi, hFixed, hKfixed, hHeight, hMem,
    hImage, hImageInv, hInside, hInsideInv, hClosed, hClosedInv, ?_, ?_, ?_, ?_⟩
  · intro h hh
    exact ⟨(hAffLower h hh).1, hInverse _ _ (hAffLower h hh).1⟩
  · intro h hh
    exact ⟨(hAffLower h hh).2, hInverse _ _ (hAffLower h hh).2⟩
  · intro h hh
    exact ⟨hAffUpper h hh, hInverse _ _ (hAffUpper h hh)⟩
  · intro Q
    have hQ : K '' (S ∩ H0 ⁻¹' Q) = S ∩ H0 ⁻¹' (g '' Q) := by
      apply Set.Subset.antisymm
      · rintro y ⟨x, ⟨hxS, hxQ⟩, rfl⟩
        exact ⟨(hMem x).1.mpr hxS, H0 x, hxQ, (hHeight x).1.symm⟩
      · rintro y ⟨hyS, a, haQ, hay⟩
        refine ⟨K.symm y, ⟨(hMem y).2.mpr hyS, ?_⟩, K.apply_symm_apply y⟩
        change H0 (K.symm y) ∈ Q
        rw [(hHeight y).2, ← hay, g.symm_apply_apply]
        exact haQ
    refine ⟨hQ, ?_⟩
    rw [← hQ]
    exact K.symm_image_image _

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
