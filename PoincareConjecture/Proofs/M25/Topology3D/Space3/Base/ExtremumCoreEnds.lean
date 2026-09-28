import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreHeightBarriers
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreComplement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCompactSurfaceFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreExtrema
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.morse_rest_cap_sign_and_unique
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
    (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -kappa) ∧
      ∀ a b : Fin S.capCount, S.owner a = i → S.owner b = i → a = b := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let s : Fin S.capCount → ℝ := fun a =>
    (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  let z0 : ℝ := c + 2 * kappa * rho ^ 2
  let flow : E3 → ℝ → E3 := boundedFlow V hL hM
  have hbar := S.morse_rest_height_barriers i F rho hrho hsmall hsource hbufferCore
    havoid c kappa hkappa hform hlower hupper V hV hVc L M hL hM U hU hrestU
    hunit hsphere
  obtain ⟨himages, _hnewImage⟩ :=
    S.morse_rest_seam_middle_images i F rho hrho hsmall hsource hbufferCore havoid
      c kappa hkappa hform hlower hupper V hV hVc L M hL hM U hU hrestU hunit hsphere
  obtain ⟨_hK, _hconn, _hdef, _hcover, hinter⟩ := S.retainedCore_geometry i
  have hseam (a : Fin S.capCount) (ha : S.owner a = i)
      (x : E3) (hx : x ∈ (S.cap a).seam) :
      x ∈ rest ∧ ⟪(u : E3), x⟫_ℝ = s a := by
    have hxc : x ∈ S.retainedCore i ∩ (S.cap a).cap := (hinter a ha).ge hx
    have hn : (S.cap a).sign ≠ 0 := by
      intro hz
      have h := (S.cap a).sign_abs
      rw [hz, abs_zero] at h
      norm_num at h
    have hh := ((S.cap a).cap_seam_signed_height x hxc.2).2.1.mpr hx
    refine ⟨⟨hxc.1, ?_⟩, sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hn)⟩
    intro hxO
    exact disjoint_left.mp (havoid a)
      (image_mono (image_mono ball_subset_closedBall) hxO) hxc.2
  have hwitness (a : Fin S.capCount) (ha : S.owner a = i) :
      ∃ x ∈ (S.cap a).seam, x ∈ rest ∧ ⟪(u : E3), x⟫_ℝ = s a := by
    obtain ⟨q, hq⟩ := (S.cap a).sourceSeam_isConnected.nonempty
    have hx : psi (S.owner a) (q, 0) ∈ (S.cap a).seam := ⟨q, hq, rfl⟩
    exact ⟨_, hx, hseam a ha _ hx⟩
  have hsign (a : Fin S.capCount) (ha : S.owner a = i) :
      (S.cap a).sign = -kappa := by
    obtain ⟨x, _hx, hxR, hh⟩ := hwitness a ha
    have hb := (hbar x hxR).1
    rw [hh] at hb
    have hk : kappa = 1 ∨ kappa = -1 := by
      apply abs_eq_abs.mp
      simpa only [abs_one] using hkappa
    have hs : (S.cap a).sign = 1 ∨ (S.cap a).sign = -1 := by
      apply abs_eq_abs.mp
      simpa only [abs_one] using (S.cap a).sign_abs
    rcases hk with hk | hk <;> rcases hs with hs | hs
    · have hl := hlower a ha hs
      change s a + 3 * D < c at hl
      rw [hk, one_mul, one_mul] at hb
      nlinarith only [hb, hl, S.buffer_pos, sq_nonneg rho]
    · simpa only [hk] using hs
    · simpa only [hk, neg_neg] using hs
    · have hu := hupper a ha hs
      change c + 3 * D < s a at hu
      rw [hk, neg_one_mul, neg_one_mul] at hb
      nlinarith only [hb, hu, S.buffer_pos, sq_nonneg rho]
  refine ⟨hsign, ?_⟩
  intro a b ha hb
  obtain ⟨xa, hxa, hxaR, hxaH⟩ := hwitness a ha
  obtain ⟨yb, _hyb, hybR, hybH⟩ := hwitness b hb
  have hab := (hbar yb hybR).2 a ha
  have hba := (hbar xa hxaR).2 b hb
  rw [hybH, hsign a ha] at hab
  rw [hxaH, hsign b hb] at hba
  have hn : -kappa ≠ 0 := by
    intro hz
    have hk : kappa = 0 := neg_eq_zero.mp hz
    rw [hk, abs_zero] at hkappa
    norm_num at hkappa
  have hs : s a = s b := by
    have he : -kappa * (s a - s b) = 0 := by nlinarith only [hab, hba]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)
  have himage (a : Fin S.capCount) (ha : S.owner a = i) :
      (fun x => flow x (z0 - s a)) '' (S.cap a).seam =
        collarHeightLevel (psi i) (u : E3) z0 := (himages a ha).2.2.2.2
  have hximage : flow xa (z0 - s a) ∈
      (fun x => flow x (z0 - s b)) '' (S.cap b).seam := by
    rw [himage b hb, ← himage a ha]
    exact ⟨xa, hxa, rfl⟩
  obtain ⟨xb, hxb, heq⟩ := hximage
  have hxab : xb = xa := by
    apply boundedFlow_injective V hL hM (z0 - s a)
    change flow xb (z0 - s a) = flow xa (z0 - s a)
    simpa only [hs] using heq
  by_contra hne
  have hxac := ((hinter a ha).ge hxa).2
  have hxbc := ((hinter b hb).ge hxb).2
  exact disjoint_left.mp (S.caps_disjoint hne) hxac (hxab ▸ hxbc)

theorem FamilyCutState.exists_morse_core_one_end
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
    let nativeHeight : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), j q⟫_ℝ
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let seamHeight : Fin S.capCount → ℝ := fun a =>
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
    let s : ℝ := c + kappa * rho ^ 2
    let z0 : ℝ := c + 2 * kappa * rho ^ 2
    ∃ (a : Fin S.capCount) (q : UnitTwoSphere),
      S.owner a = i ∧ (S.cap a).sign = -kappa ∧
      (∀ b : Fin S.capCount, S.owner b = i ↔ b = a) ∧
      Fintype.card {b : Fin S.capCount // S.owner b = i} = 1 ∧
      F 0 ∈ S.sourceCore i ∧ q ∈ S.sourceCore i ∧
      q ∈ (S.cap a).sourceSeam ∧ nativeHeight (F 0) = c ∧
      IsMinOn (fun p : UnitTwoSphere => kappa * nativeHeight p)
        (S.sourceCore i) (F 0) ∧
      IsMaxOn (fun p : UnitTwoSphere => kappa * nativeHeight p)
        (S.sourceCore i) q ∧
      (∀ p ∈ (S.cap a).sourceSeam, nativeHeight p = seamHeight a) ∧
      0 < kappa * (s - c) ∧ 0 < kappa * (z0 - s) ∧
      0 < kappa * (seamHeight a - z0) ∧
      (∀ p ∈ S.sourceCore i,
        0 ≤ kappa * (nativeHeight p - c) ∧
          kappa * (nativeHeight p - c) ≤ kappa * (seamHeight a - c)) ∧
      (∀ p ∈ S.sourceCore i, nativeHeight p = c ↔ p = F 0) ∧
      ∀ y ∈ rest,
        0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
          kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ kappa * (seamHeight a - s) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), j q⟫_ℝ
  let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let seamHeight : Fin S.capCount → ℝ := fun a =>
    (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  let s : ℝ := c + kappa * rho ^ 2
  let z0 : ℝ := c + 2 * kappa * rho ^ 2
  let K := S.sourceCore i
  let nativeRest := K \ F '' ball (0 : E2) rho
  have hsub : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  have hsource' := hsub.trans hsource
  have hdisc : F '' closedBall (0 : E2) rho ⊆ S.sourceCore i :=
    (image_mono hsub).trans hbufferCore
  obtain ⟨hRc, _hRn, _hnot, hreg, _hnative, hRimage, _hLc, _hLn,
    _hcover, _hnew, _hold, _havoid⟩ :=
    S.morse_disc_complement_geometry i F rho hrho hsource' hdisc havoid hunique
  obtain ⟨rho0, _hrho0, _hrhopsi, _hrhon, N, _hN, hRN, _hNU, _hnormal,
    V, hV, hVc, _hsupport, _hfirst, hheight, L, M, hL, hM, _hsmooth,
    hpreserve, _hfix⟩ :=
    exists_regular_compact_surface_flow (psi i) (S.embedding i) u nativeRest hRc hreg
  have hrestU : rest ⊆ interior N := by
    change S.retainedCore i \ j '' (F '' ball (0 : E2) rho) ⊆ interior N
    rw [← hRimage]
    exact hRN
  have hunit : ∀ y ∈ interior N, ⟪(u : E3), V y⟫_ℝ = 1 :=
    fun y hy => hheight y (interior_subset hy)
  have hsphere : ∀ y ∈ range j, ∀ t : ℝ, boundedFlow V hL hM y t ∈ range j := by
    intro y hy t
    rw [← hpreserve t]
    exact ⟨y, hy, rfl⟩
  have hbar := S.morse_rest_height_barriers i F rho hrho hsmall hsource hbufferCore
    havoid c kappa hkappa hform hlower hupper V hV hVc L M hL hM (interior N)
    isOpen_interior hrestU hunit hsphere
  obtain ⟨hsign, hsame⟩ :=
    S.morse_rest_cap_sign_and_unique i F rho hrho hsmall hsource hbufferCore havoid
      c kappa hkappa hform hlower hupper V hV hVc L M hL hM (interior N)
      isOpen_interior hrestU hunit hsphere
  have hkap2 : kappa ^ 2 = 1 := by nlinarith only [sq_abs kappa, hkappa]
  have hkap : kappa = 1 ∨ kappa = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using hkappa
  have hzero : (0 : E2) ∈ closedBall (0 : E2) (2 * rho) := by
    rw [mem_closedBall_zero_iff, norm_zero]
    linarith only [hrho]
  have hFzero : F 0 ∈ K := hbufferCore ⟨0, hzero, rfl⟩
  have hfzero : f (F 0) = c := by
    simpa only [f, j, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
      using hform 0 hzero
  have hj : Continuous j := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hf : Continuous f := continuous_const.inner hj
  have hg : Continuous (fun p : UnitTwoSphere => kappa * f p) := continuous_const.mul hf
  have hjinj : Function.Injective j := by
    intro p q hpq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hpq)
  obtain ⟨hKc, hKn⟩ := S.sourceCore_compact_connected i
  obtain ⟨_hzeroO, _hOD, _hDt, _hO, _hD, _hSc, hSn, _hclosure, _hdiff,
    _hfrontier⟩ := nativeDiscChart_geometry F rho hrho hsource'
  obtain ⟨p, hpSeam⟩ := hSn.nonempty
  obtain ⟨x, hx, rfl⟩ := hpSeam
  have hxbuf := hsub (sphere_subset_closedBall hx)
  have hpK : F x ∈ K := hbufferCore ⟨x, hxbuf, rfl⟩
  have hpheight : kappa * f (F x) - kappa * c = rho ^ 2 := by
    change kappa * ⟪(u : E3), psi i (F x, 0)⟫_ℝ - kappa * c = rho ^ 2
    rw [hform x hxbuf, mem_sphere_zero_iff_norm.mp hx]
    calc
      _ = kappa ^ 2 * rho ^ 2 := by ring
      _ = rho ^ 2 := by rw [hkap2, one_mul]
  obtain ⟨q, hqK, hmax⟩ := hKc.exists_isMaxOn hKn.nonempty hg.continuousOn
  have hqstrict : kappa * c < kappa * f q := by
    have hmaxp : kappa * f (F x) ≤ kappa * f q := hmax hpK
    have hrhosq := sq_pos_of_pos hrho
    linarith only [hmaxp, hpheight, hrhosq]
  have hqne : q ≠ F 0 := by
    intro hq
    rw [hq, hfzero] at hqstrict
    exact (lt_irrefl _) hqstrict
  have hqregular : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0 :=
    fun hz => hqne (hunique q hqK hz)
  have hextreme : IsMinOn f K q ∨ IsMaxOn f K q := by
    rcases hkap with hk | hk
    · right
      intro p hp
      have hh : kappa * f p ≤ kappa * f q := hmax hp
      change f p ≤ f q
      simpa only [hk, one_mul] using hh
    · left
      intro p hp
      have hh : kappa * f p ≤ kappa * f q := hmax hp
      change f q ≤ f p
      rw [hk, neg_one_mul, neg_one_mul] at hh
      linarith only [hh]
  obtain ⟨a, ha, hqSeam, hseamHeight⟩ :=
    S.sourceCore_extremum_on_seam i q hqK hqregular hextreme
  have howner (b : Fin S.capCount) : S.owner b = i ↔ b = a := by
    constructor
    · intro hb
      exact hsame b a hb ha
    · rintro rfl
      exact ha
  have hcard : Fintype.card {b : Fin S.capCount // S.owner b = i} = 1 := by
    let g : Fin 1 → {b : Fin S.capCount // S.owner b = i} := fun _ => ⟨a, ha⟩
    have hgBij : Function.Bijective g := by
      constructor
      · intro b d _hbd
        exact Subsingleton.elim b d
      · intro b
        refine ⟨0, ?_⟩
        apply Subtype.ext
        exact (howner b.1).mp b.2 |>.symm
    exact (Fintype.card_congr (Equiv.ofBijective g hgBij)).symm.trans (Fintype.card_fin 1)
  have hrelative : kappa * (s - c) = rho ^ 2 := by
    calc
      _ = kappa ^ 2 * rho ^ 2 := by dsimp only [s]; ring
      _ = rho ^ 2 := by rw [hkap2, one_mul]
  have hzrelative : kappa * (z0 - s) = rho ^ 2 := by
    calc
      _ = kappa ^ 2 * rho ^ 2 := by dsimp only [z0, s]; ring
      _ = rho ^ 2 := by rw [hkap2, one_mul]
  have houtside (p : UnitTwoSphere) (hp : p ∈ K)
      (hpO : p ∉ F '' ball (0 : E2) rho) : 0 < kappa * (f p - c) := by
    have hpR : j p ∈ rest := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro ⟨p', hp', heq⟩
      exact hpO ((hjinj heq) ▸ hp')
    have hb := (hbar (j p) hpR).1
    change 0 ≤ kappa * (f p - s) at hb
    have hsum : kappa * (f p - c) = kappa * (f p - s) + rho ^ 2 := by
      calc
        _ = kappa * (f p - s) + kappa * (s - c) := by ring
        _ = _ := by rw [hrelative]
    rw [hsum]
    exact add_pos_of_nonneg_of_pos hb (sq_pos_of_pos hrho)
  have hinside (x : E2) (hx : x ∈ ball (0 : E2) rho) :
      kappa * (f (F x) - c) = ‖x‖ ^ 2 := by
    change kappa * (⟪(u : E3), psi i (F x, 0)⟫_ℝ - c) = ‖x‖ ^ 2
    rw [hform x (hsub (ball_subset_closedBall hx))]
    calc
      _ = kappa ^ 2 * ‖x‖ ^ 2 := by ring
      _ = _ := by rw [hkap2, one_mul]
  have hlowerCore (p : UnitTwoSphere) (hp : p ∈ K) : 0 ≤ kappa * (f p - c) := by
    by_cases hpO : p ∈ F '' ball (0 : E2) rho
    · obtain ⟨x, hx, rfl⟩ := hpO
      rw [hinside x hx]
      exact sq_nonneg ‖x‖
    · exact (houtside p hp hpO).le
  have hfiber (p : UnitTwoSphere) (hp : p ∈ K) : f p = c ↔ p = F 0 := by
    constructor
    · intro hpc
      by_cases hpO : p ∈ F '' ball (0 : E2) rho
      · obtain ⟨x, hx, rfl⟩ := hpO
        have hnorm := hinside x hx
        rw [hpc, sub_self, mul_zero] at hnorm
        have hxzero : x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm.symm)
        rw [hxzero]
      · have hstrict := houtside p hp hpO
        rw [hpc, sub_self, mul_zero] at hstrict
        exact (lt_irrefl 0 hstrict).elim
    · rintro rfl
      exact hfzero
  have hmin : IsMinOn (fun p : UnitTwoSphere => kappa * f p) K (F 0) := by
    intro p hp
    change kappa * f (F 0) ≤ kappa * f p
    rw [hfzero]
    have hh := hlowerCore p hp
    nlinarith only [hh]
  have hqHeight : f q = seamHeight a := hseamHeight q hqSeam
  have hupperCore (p : UnitTwoSphere) (hp : p ∈ K) :
      kappa * (f p - c) ≤ kappa * (seamHeight a - c) := by
    have hh : kappa * f p ≤ kappa * f q := hmax hp
    rw [hqHeight] at hh
    nlinarith only [hh]
  have hmiddle : 0 < kappa * (seamHeight a - z0) := by
    obtain ⟨_hdc, _hsc, _hsn, _hdiff, _hzsmall, _hzside, hlo, hup, _hfull, _hmiss⟩ :=
      S.morse_disc_middle_geometry i F rho hrho hsmall hsource' c kappa hkappa
        (fun x hx => hform x (hsub hx)) hlower hupper
    rcases hkap with hk | hk
    · have hs : (S.cap a).sign = -1 := by simpa only [hk] using hsign a ha
      have hh := hup a ha hs
      change z0 < seamHeight a at hh
      rw [hk, one_mul]
      exact sub_pos.mpr hh
    · have hs : (S.cap a).sign = 1 := by simpa only [hk, neg_neg] using hsign a ha
      have hh := hlo a ha hs
      change seamHeight a < z0 at hh
      rw [hk, neg_one_mul]
      linarith only [hh]
  refine ⟨a, q, ha, hsign a ha, howner, hcard, hFzero, hqK, hqSeam, hfzero,
    hmin, hmax, hseamHeight, ?_, ?_, hmiddle, ?_, hfiber, ?_⟩
  · rw [hrelative]
    exact sq_pos_of_pos hrho
  · rw [hzrelative]
    exact sq_pos_of_pos hrho
  · intro p hp
    exact ⟨hlowerCore p hp, hupperCore p hp⟩
  · intro y hy
    refine ⟨(hbar y hy).1, ?_⟩
    obtain ⟨p, hp, hpy⟩ := hy.1
    change j p = y at hpy
    have hh := hupperCore p hp
    change kappa * (⟪(u : E3), j p⟫_ℝ - c) ≤ kappa * (seamHeight a - c) at hh
    rw [hpy] at hh
    change kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ kappa * (seamHeight a - s)
    nlinarith only [hh]

end PoincareConjecture.M25.Topology3D
