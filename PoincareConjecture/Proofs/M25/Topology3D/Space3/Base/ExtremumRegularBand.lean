import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreEnds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsLevels

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.exists_morse_rest_regular_band
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : 2 * rho ^ 2 < D)
    (hsource : closedBall (0 : E2) (2 * rho) ⊆ F.source)
    (hbufferCore : F '' closedBall (0 : E2) (2 * rho) ⊆ S.sourceCore i)
    (havoid : ∀ a : Fin S.capCount,
      Disjoint ((fun q : UnitTwoSphere => psi i (q, 0)) ''
        (F '' closedBall (0 : E2) rho)) (S.cap a).cap)
    (c kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ x ∈ closedBall (0 : E2) (2 * rho),
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2)
    (hunique : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0 →
          q = F 0)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal + 3 * D < c)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let nativeRest : Set UnitTwoSphere := S.sourceCore i \ (F '' ball (0 : E2) rho)
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let s : ℝ := c + kappa * rho ^ 2
    let seamHeight : Fin S.capCount → ℝ := fun a =>
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
    ∃ a : Fin S.capCount,
      S.owner a = i ∧ (S.cap a).sign = -kappa ∧
      (∀ b : Fin S.capCount, S.owner b = i ↔ b = a) ∧
      Fintype.card {b : Fin S.capCount // S.owner b = i} = 1 ∧
      let ell : ℝ := min s (seamHeight a)
      let upper : ℝ := max s (seamHeight a)
      ell < upper ∧
      (kappa = 1 → ell = s ∧ upper = seamHeight a) ∧
      (kappa = -1 → ell = seamHeight a ∧ upper = s) ∧
      rest = j '' nativeRest ∧ IsCompact rest ∧ IsConnected rest ∧
      (∀ q ∈ nativeRest,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) ∧
      rest = {y : E3 | y ∈ range j ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} ∧
      (∀ q : UnitTwoSphere, j q ∈ rest →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) ∧
      collarHeightLevel (psi i) (u : E3) s =
        j '' (F '' sphere (0 : E2) rho) ∧
      collarHeightLevel (psi i) (u : E3) (seamHeight a) = (S.cap a).seam := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let nativeRest := S.sourceCore i \ (F '' ball (0 : E2) rho)
  let rest := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let disc := j '' (F '' closedBall (0 : E2) rho)
  let newSeam := j '' (F '' sphere (0 : E2) rho)
  let s := c + kappa * rho ^ 2
  let z0 := c + 2 * kappa * rho ^ 2
  let seamHeight : Fin S.capCount → ℝ := fun a =>
    (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  obtain ⟨a, _q, ha, hsign, howner, hcard, _hF0, _hqCore, _hqSeam,
    _hzero, _hmin, _hmax, _hseamHeight, _hs0, hzside, hzold,
    _hcoreBounds, _hcritical, hbounds⟩ :=
    S.exists_morse_core_one_end i F rho hrho hsmall hsource hbufferCore havoid
      c kappa hkappa hform hunique hlower hupper
  change 0 < kappa * (z0 - s) at hzside
  change 0 < kappa * (seamHeight a - z0) at hzold
  change ∀ y ∈ rest, 0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
    kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ kappa * (seamHeight a - s) at hbounds
  let ell := min s (seamHeight a)
  let upper := max s (seamHeight a)
  have hkap : kappa = 1 ∨ kappa = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using hkappa
  have hkapne : kappa ≠ 0 := by
    intro h
    rw [h, abs_zero] at hkappa
    norm_num at hkappa
  have hposOrder (hk : kappa = 1) : s < seamHeight a := by
    rw [hk, one_mul] at hzside hzold
    linarith only [hzside, hzold]
  have hnegOrder (hk : kappa = -1) : seamHeight a < s := by
    rw [hk, neg_one_mul] at hzside hzold
    linarith only [hzside, hzold]
  have hpositive (hk : kappa = 1) : ell = s ∧ upper = seamHeight a :=
    ⟨min_eq_left (hposOrder hk).le, max_eq_right (hposOrder hk).le⟩
  have hnegative (hk : kappa = -1) : ell = seamHeight a ∧ upper = s :=
    ⟨min_eq_right (hnegOrder hk).le, max_eq_left (hnegOrder hk).le⟩
  have horder : ell < upper := by
    rcases hkap with hk | hk
    · rw [(hpositive hk).1, (hpositive hk).2]
      exact hposOrder hk
    · rw [(hnegative hk).1, (hnegative hk).2]
      exact hnegOrder hk
  have hinterval (v : ℝ) : v ∈ Icc ell upper ↔
      0 ≤ kappa * (v - s) ∧ kappa * (v - seamHeight a) ≤ 0 := by
    rcases hkap with hk | hk
    · simp only [mem_Icc, (hpositive hk).1, (hpositive hk).2, hk, one_mul]
      constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith only [hl, hu]
    · simp only [mem_Icc, (hnegative hk).1, (hnegative hk).2, hk, neg_one_mul]
      constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith only [hl, hu]
  have hsub : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  have hsource' := hsub.trans hsource
  have hdisc : F '' closedBall (0 : E2) rho ⊆ S.sourceCore i :=
    (image_mono hsub).trans hbufferCore
  have hform' (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2 := hform x (hsub hx)
  obtain ⟨hRc, _hRn, _hnot, hreg, _hnative, hRimage, hLc, hLn,
    hcover, hnew, hold, _hdisjoint⟩ :=
    S.morse_disc_complement_geometry i F rho hrho hsource' hdisc havoid hunique
  change IsCompact nativeRest at hRc
  change ∀ q ∈ nativeRest, mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0 at hreg
  change j '' nativeRest = rest at hRimage
  have hcompact : IsCompact rest := hRimage ▸ hLc
  have hconnected : IsConnected rest := hRimage ▸ hLn
  change range j = ((j '' nativeRest) ∪ disc) ∪
    (⋃ b : {b : Fin S.capCount // S.owner b = i}, (S.cap b.1).cap) at hcover
  rw [hRimage] at hcover
  change (j '' nativeRest) ∩ disc = newSeam at hnew
  rw [hRimage] at hnew
  change ∀ b : Fin S.capCount, S.owner b = i →
    (j '' nativeRest) ∩ (S.cap b).cap = (S.cap b).seam at hold
  rw [hRimage] at hold
  have hjinj : Function.Injective j := by
    intro p q hpq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hpq)
  have hrestRange : rest ⊆ range j := by
    intro y hy
    rw [← hRimage] at hy
    obtain ⟨q, _hq, heq⟩ := hy
    exact ⟨q, heq⟩
  have hregular (q : UnitTwoSphere) (hq : j q ∈ rest) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0 := by
    rw [← hRimage] at hq
    obtain ⟨p, hp, heq⟩ := hq
    exact (hjinj heq) ▸ hreg p hp
  obtain ⟨_hdiscC, _hseamC, _hseamConn, _hdiff, _hzsmall, _hzside,
    _hlower, _hupper, hfull, _hmiss⟩ :=
    S.morse_disc_middle_geometry i F rho hrho hsmall hsource' c kappa hkappa
      hform' hlower hupper
  have hband : rest =
      {y : E3 | y ∈ range j ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} := by
    ext y
    constructor
    · intro hy
      obtain ⟨hl, hu⟩ := hbounds y hy
      refine ⟨hrestRange hy, (hinterval _).mpr ⟨hl, ?_⟩⟩
      nlinarith only [hu]
    · rintro ⟨hy, hh⟩
      have hb := (hinterval _).mp hh
      rw [hcover] at hy
      rcases hy with (hyR | hyD) | hyC
      · exact hyR
      · have hd := hfull y hyD
        have hle : kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ 0 := hd.2.2.1
        have heq : ⟪(u : E3), y⟫_ℝ = s :=
          sub_eq_zero.mp ((mul_eq_zero.mp (le_antisymm hle hb.1)).resolve_left hkapne)
        have hseam : y ∈ newSeam := hd.2.2.2.1.mp heq
        exact (hnew.ge hseam).1
      · obtain ⟨b, hbC⟩ := mem_iUnion.mp hyC
        have hba : b.1 = a := (howner b.1).mp b.2
        have hyCap : y ∈ (S.cap a).cap := hba ▸ hbC
        have hc := (S.cap a).cap_seam_signed_height y hyCap
        have hn : 0 ≤ (S.cap a).sign * (⟪(u : E3), y⟫_ℝ - seamHeight a) := by
          rw [hsign, neg_mul]
          exact neg_nonneg.mpr hb.2
        have hseam : y ∈ (S.cap a).seam := hc.2.1.mp (le_antisymm hc.1 hn)
        exact ((hold a ha).ge hseam).1
  obtain ⟨rho0, _hrho0, _hrhopsi, _hrhon, N, _hN, hRN, _hNU, _hnormal,
    V, hV, hVc, _hsupport, _hfirst, hheight, L, M, hL, hM, _hsmooth,
    hpreserve, _hfix⟩ :=
    exists_regular_compact_surface_flow (psi i) (S.embedding i) u nativeRest hRc hreg
  have hrestU : rest ⊆ interior N := by
    rw [← hRimage]
    exact hRN
  have hunit : ∀ y ∈ interior N, ⟪(u : E3), V y⟫_ℝ = 1 :=
    fun y hy => hheight y (interior_subset hy)
  have hsphere : ∀ y ∈ range j, ∀ t : ℝ, boundedFlow V hL hM y t ∈ range j := by
    intro y hy t
    rw [← hpreserve t]
    exact ⟨y, hy, rfl⟩
  let flow := boundedFlow V hL hM
  let Z := collarHeightLevel (psi i) (u : E3) z0
  let R : E3 → E3 := fun y => flow y (z0 - ⟪(u : E3), y⟫_ℝ)
  obtain ⟨_hR, hRZ, _hRfix, _hZc, _hZn⟩ :=
    S.morse_rest_middle_retraction i F rho hrho hsmall hsource' hdisc c kappa hkappa
      hform' hlower hupper V hV hVc L M hL hM (interior N) isOpen_interior
        hrestU hunit hsphere
  change R '' rest = Z at hRZ
  obtain ⟨holdImages, hnewImage⟩ :=
    S.morse_rest_seam_middle_images i F rho hrho hsmall hsource hbufferCore havoid
      c kappa hkappa hform hlower hupper V hV hVc L M hL hM (interior N)
        isOpen_interior hrestU hunit hsphere
  have hnewFull : (fun y : E3 => flow y (z0 - s)) '' newSeam = Z :=
    hnewImage.2.2.2.2
  have holdFull : (fun y : E3 => flow y (z0 - seamHeight a)) '' (S.cap a).seam = Z :=
    (holdImages a ha).2.2.2.2
  have hlevel (t : ℝ) (y : E3) : y ∈ collarHeightLevel (psi i) (u : E3) t ↔
      y ∈ range j ∧ ⟪(u : E3), y⟫_ℝ = t := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, hq⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, hq, rfl⟩
  have hendpoint (Sigma : Set E3) (t : ℝ) (ht : t ∈ Icc ell upper)
      (hSigma : Sigma ⊆ rest) (hH : ∀ y ∈ Sigma, ⟪(u : E3), y⟫_ℝ = t)
      (hfullImage : (fun y : E3 => flow y (z0 - t)) '' Sigma = Z) :
      collarHeightLevel (psi i) (u : E3) t = Sigma := by
    apply subset_antisymm
    · intro y hy
      obtain ⟨hyj, hyt⟩ := (hlevel t y).mp hy
      have hyr : y ∈ rest := hband.symm ▸ ⟨hyj, hyt.symm ▸ ht⟩
      have hyZ : R y ∈ Z := hRZ ▸ mem_image_of_mem R hyr
      rw [← hfullImage] at hyZ
      obtain ⟨x, hx, heq⟩ := hyZ
      have hsame : flow x (z0 - t) = flow y (z0 - t) := by
        simpa only [R, hyt] using heq
      exact (boundedFlow_injective V hL hM (z0 - t) hsame) ▸ hx
    · intro y hy
      exact (hlevel t y).mpr ⟨hrestRange (hSigma hy), hH y hy⟩
  have hnewLevel : collarHeightLevel (psi i) (u : E3) s = newSeam := by
    apply hendpoint newSeam s ⟨min_le_left _ _, le_max_left _ _⟩
      (fun y hy => (hnew.ge hy).1) _ hnewFull
    intro y hy
    exact (hfull y (hnew.ge hy).2).2.2.2.1.mpr hy
  have holdLevel : collarHeightLevel (psi i) (u : E3) (seamHeight a) =
      (S.cap a).seam := by
    apply hendpoint (S.cap a).seam (seamHeight a) ⟨min_le_right _ _, le_max_right _ _⟩
      (fun y hy => ((hold a ha).ge hy).1) _ holdFull
    intro y hy
    have hz := ((S.cap a).cap_seam_signed_height y ((hold a ha).ge hy).2).2.1.mpr hy
    have hsne : (S.cap a).sign ≠ 0 := by
      rw [hsign]
      exact neg_ne_zero.mpr hkapne
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hsne)
  exact ⟨a, ha, hsign, howner, hcard, horder, hpositive, hnegative, hRimage.symm,
    hcompact, hconnected, hreg, hband, hregular, hnewLevel, holdLevel⟩

theorem FamilyCutState.exists_morse_rest_circle_family
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : 2 * rho ^ 2 < D)
    (hsource : closedBall (0 : E2) (2 * rho) ⊆ F.source)
    (hbufferCore : F '' closedBall (0 : E2) (2 * rho) ⊆ S.sourceCore i)
    (havoid : ∀ a : Fin S.capCount,
      Disjoint ((fun q : UnitTwoSphere => psi i (q, 0)) ''
        (F '' closedBall (0 : E2) rho)) (S.cap a).cap)
    (c kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ x ∈ closedBall (0 : E2) (2 * rho),
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2)
    (hunique : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0 →
          q = F 0)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal + 3 * D < c)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let nativeRest : Set UnitTwoSphere := S.sourceCore i \ (F '' ball (0 : E2) rho)
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let s : ℝ := c + kappa * rho ^ 2
    let seamHeight : Fin S.capCount → ℝ := fun a =>
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
    ∃ a : Fin S.capCount,
      S.owner a = i ∧ (S.cap a).sign = -kappa ∧
      (∀ b : Fin S.capCount, S.owner b = i ↔ b = a) ∧
      Fintype.card {b : Fin S.capCount // S.owner b = i} = 1 ∧
      let ell : ℝ := min s (seamHeight a)
      let upper : ℝ := max s (seamHeight a)
      ell < upper ∧
      (kappa = 1 → ell = s ∧ upper = seamHeight a) ∧
      (kappa = -1 → ell = seamHeight a ∧ upper = s) ∧
      rest = j '' nativeRest ∧ IsCompact rest ∧ IsConnected rest ∧
      (∀ q ∈ nativeRest,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) ∧
      rest = {y : E3 | y ∈ range j ∧ ⟪(u : E3), y⟫_ℝ ∈ Icc ell upper} ∧
      (∀ q : UnitTwoSphere, j q ∈ rest →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) ∧
      collarHeightLevel (psi i) (u : E3) s =
        j '' (F '' sphere (0 : E2) rho) ∧
      collarHeightLevel (psi i) (u : E3) (seamHeight a) = (S.cap a).seam ∧
      ∃ eta : ℝ, 0 < eta ∧ ∃ gamma : ℝ → UnitCircle → E2,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
          (fun p : ℝ × UnitCircle => gamma p.1 p.2) ∧
        (∀ z ∈ Icc (ell - eta) (upper + eta), IsPlanarEmbedding (gamma z)) ∧
        ∀ z ∈ Icc (ell - eta) (upper + eta),
          range (gamma z) = {x : E2 |
            (heightPlaneCoordinates u).symm (x, z) ∈ range j} := by
  obtain ⟨a, ha, hsign, howner, hcard, horder, hpositive, hnegative, himage,
    hcompact, hconnected, hreg, hband, hregular, hnewLevel, holdLevel⟩ :=
    S.exists_morse_rest_regular_band i F rho hrho hsmall hsource hbufferCore havoid
      c kappa hkappa hform hunique hlower hupper
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let s := c + kappa * rho ^ 2
  let haHeight := (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  let rest := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  obtain ⟨eta, heta, gamma, hgamma, hemb, hlevels⟩ :=
    exists_stackCircleFamily_of_connected_regular_band (psi i) (S.embedding i) u
      (min s haHeight) (max s haHeight) horder rest hconnected hband hregular
  exact ⟨a, ha, hsign, howner, hcard, horder, hpositive, hnegative, himage,
    hcompact, hconnected, hreg, hband, hregular, hnewLevel, holdLevel,
    eta, heta, gamma, hgamma, hemb, hlevels⟩

end PoincareConjecture.M25.Topology3D
