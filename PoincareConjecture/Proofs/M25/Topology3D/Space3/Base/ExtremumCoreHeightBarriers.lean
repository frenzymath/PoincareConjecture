import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreSeamNeighborhoods
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreSeamFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreTransport










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.morse_rest_height_barriers
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
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let seamHeight : Fin S.capCount → ℝ := fun a =>
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
    let s : ℝ := c + kappa * rho ^ 2
    ∀ y ∈ rest,
      0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
      ∀ a : Fin S.capCount, S.owner a = i →
        0 ≤ (S.cap a).sign * (⟪(u : E3), y⟫_ℝ - seamHeight a) := by
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let seamHeight : Fin S.capCount → ℝ := fun a =>
    (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  let s : ℝ := c + kappa * rho ^ 2
  let z0 : ℝ := c + 2 * kappa * rho ^ 2
  let Z : Set E3 := collarHeightLevel (psi i) (u : E3) z0
  let flow : E3 → ℝ → E3 := boundedFlow V hL hM
  have hsub : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  have hsource' := hsub.trans hsource
  have hform' := fun x hx => hform x (hsub hx)
  obtain ⟨_hdc, _hsc, _hsn, _hdiff, _hzsmall, hzside, hlo, hup, _hfull, _hmiss⟩ :=
    S.morse_disc_middle_geometry i F rho hrho hsmall hsource' c kappa hkappa
      hform' hlower hupper
  obtain ⟨holdImages, hnewImage⟩ :=
    S.morse_rest_seam_middle_images i F rho hrho hsmall hsource hbufferCore havoid
      c kappa hkappa hform hlower hupper V hV hVc L M hL hM U hU hrestU hunit hsphere
  have hsegment (y : E3) (hy : y ∈ rest) (t : ℝ)
      (ht : t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ)) :
      flow y t ∈ rest ∧ ⟪(u : E3), flow y t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t :=
    S.morse_rest_flow_segment i F rho hrho hsmall hsource' c kappa hkappa hform'
      hlower hupper V L M hL hM U hU hrestU hunit hsphere y hy t ht
  have hsurface (y : E3) (hy : y ∈ rest) : y ∈ range j := by
    obtain ⟨q, _hq, hqy⟩ := hy.1
    exact ⟨q, hqy⟩
  have hcurve (y : E3) : Continuous (flow y) :=
    (boundedFlow_contDiff V hL hM hV hVc).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hbarrier (Sigma : Set E3) (s0 sigma : ℝ) (hsigma : |sigma| = 1)
      (hside : 0 < sigma * (z0 - s0))
      (himage : (fun x => flow x (z0 - s0)) '' Sigma = Z)
      (hlocal : ∀ x ∈ Sigma, ∃ O : Set E3, IsOpen O ∧ x ∈ O ∧
        ∀ p ∈ O, p ∈ rest → 0 ≤ sigma * (⟪(u : E3), p⟫_ℝ - s0))
      (y : E3) (hy : y ∈ rest) : 0 ≤ sigma * (⟪(u : E3), y⟫_ℝ - s0) := by
    have hb : flow y (z0 - ⟪(u : E3), y⟫_ℝ) ∈ Z := by
      obtain ⟨q, hq⟩ := hsphere y (hsurface y hy) (z0 - ⟪(u : E3), y⟫_ℝ)
      change psi i (q, 0) = flow y (z0 - ⟪(u : E3), y⟫_ℝ) at hq
      have hh := (hsegment y hy (z0 - ⟪(u : E3), y⟫_ℝ) right_mem_uIcc).2
      refine ⟨q, ?_, hq⟩
      change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0
      rw [hq]
      linarith only [hh]
    rw [← himage] at hb
    obtain ⟨x, hx, heq⟩ := hb
    change flow x (z0 - s0) = flow y (z0 - ⟪(u : E3), y⟫_ℝ) at heq
    have hhit : flow y (s0 - ⟪(u : E3), y⟫_ℝ) = x := by
      calc
        _ = flow (flow y (z0 - ⟪(u : E3), y⟫_ℝ)) (-(z0 - s0)) := by
          change boundedFlow V hL hM y (s0 - ⟪(u : E3), y⟫_ℝ) =
            boundedFlow V hL hM (boundedFlow V hL hM y
              (z0 - ⟪(u : E3), y⟫_ℝ)) (-(z0 - s0))
          rw [← boundedFlow_add]
          congr 1
          ring
        _ = flow (flow x (z0 - s0)) (-(z0 - s0)) := by rw [heq]
        _ = x := boundedFlow_neg V hL hM x (z0 - s0)
    obtain ⟨O, hO, hxO, hineq⟩ := hlocal x hx
    have hpre : IsOpen ((flow y) ⁻¹' O) := hO.preimage (hcurve y)
    obtain ⟨eta, heta, hball⟩ := Metric.isOpen_iff.mp hpre
      (s0 - ⟪(u : E3), y⟫_ℝ) (by
        change flow y (s0 - ⟪(u : E3), y⟫_ℝ) ∈ O
        rw [hhit]
        exact hxO)
    by_contra hnot
    have hneg := lt_of_not_ge hnot
    have hsign : sigma = 1 ∨ sigma = -1 := by
      apply abs_eq_abs.mp
      simpa only [abs_one] using hsigma
    rcases hsign with hsign | hsign
    · rw [hsign, one_mul] at hside hneg
      obtain ⟨eps, heps, hepslt⟩ := exists_between
        (lt_min heta (show 0 < s0 - ⟪(u : E3), y⟫_ℝ by linarith only [hneg]))
      have hepseta : eps < eta := hepslt.trans_le (min_le_left _ _)
      have hepsdelta : eps < s0 - ⟪(u : E3), y⟫_ℝ :=
        hepslt.trans_le (min_le_right _ _)
      let t := s0 - ⟪(u : E3), y⟫_ℝ - eps
      have ht : t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ) := by
        rw [uIcc_of_le (by linarith only [hside, hneg] :
          0 ≤ z0 - ⟪(u : E3), y⟫_ℝ)]
        dsimp only [t]
        constructor <;> linarith only [hepsdelta, heps, hside]
      have hpoint : flow y t ∈ O := by
        apply hball
        rw [mem_ball, Real.dist_eq]
        have ht' : t - (s0 - ⟪(u : E3), y⟫_ℝ) = -eps := by dsimp only [t]; ring
        rw [ht', abs_neg, abs_of_pos heps]
        exact hepseta
      obtain ⟨hrest, hh⟩ := hsegment y hy t ht
      have hi := hineq (flow y t) hpoint hrest
      rw [hsign, one_mul] at hi
      dsimp only [t] at hh hi
      linarith only [hi, hh, heps]
    · rw [hsign, neg_one_mul] at hside hneg
      obtain ⟨eps, heps, hepslt⟩ := exists_between
        (lt_min heta (show 0 < -(s0 - ⟪(u : E3), y⟫_ℝ) by linarith only [hneg]))
      have hepseta : eps < eta := hepslt.trans_le (min_le_left _ _)
      have hepsdelta : eps < -(s0 - ⟪(u : E3), y⟫_ℝ) :=
        hepslt.trans_le (min_le_right _ _)
      let t := s0 - ⟪(u : E3), y⟫_ℝ + eps
      have ht : t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ) := by
        rw [uIcc_of_ge (by linarith only [hside, hneg] :
          z0 - ⟪(u : E3), y⟫_ℝ ≤ 0)]
        dsimp only [t]
        constructor <;> linarith only [hepsdelta, heps, hside]
      have hpoint : flow y t ∈ O := by
        apply hball
        rw [mem_ball, Real.dist_eq]
        have ht' : t - (s0 - ⟪(u : E3), y⟫_ℝ) = eps := by dsimp only [t]; ring
        rw [ht', abs_of_pos heps]
        exact hepseta
      obtain ⟨hrest, hh⟩ := hsegment y hy t ht
      have hi := hineq (flow y t) hpoint hrest
      rw [hsign, neg_one_mul] at hi
      dsimp only [t] at hh hi
      linarith only [hi, hh, heps]
  change ∀ y ∈ rest, 0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
    ∀ a : Fin S.capCount, S.owner a = i →
      0 ≤ (S.cap a).sign * (⟪(u : E3), y⟫_ℝ - seamHeight a)
  intro y hy
  constructor
  · apply hbarrier (j '' (F '' sphere (0 : E2) rho)) s kappa hkappa hzside
      hnewImage.2.2.2.2
    · rintro x ⟨q0, hq0, rfl⟩
      obtain ⟨_hW, _hqW, _hWt, _hcoord, O, hO, hqO, _hcollar, _hOW, hlocal⟩ :=
        S.exists_morse_rest_new_seam_neighborhood i F rho hrho hsource hbufferCore
          c kappa hkappa hform q0 hq0
      refine ⟨O, hO, hqO, ?_⟩
      intro p hp hpr
      exact ((hlocal p hp (hsurface p hpr)).1).mp hpr
    · exact hy
  · intro a ha
    have hside : 0 < (S.cap a).sign * (z0 - seamHeight a) := by
      have hsign : (S.cap a).sign = 1 ∨ (S.cap a).sign = -1 := by
        apply abs_eq_abs.mp
        simpa only [abs_one] using (S.cap a).sign_abs
      rcases hsign with hsign | hsign
      · have hh := hlo a ha hsign
        change seamHeight a < z0 at hh
        rw [hsign, one_mul]
        exact sub_pos.mpr hh
      · have hh := hup a ha hsign
        change z0 < seamHeight a at hh
        rw [hsign, neg_one_mul]
        linarith only [hh]
    apply hbarrier (S.cap a).seam (seamHeight a) (S.cap a).sign (S.cap a).sign_abs
      hside (holdImages a ha).2.2.2.2
    · rintro x ⟨q0, hq0, hq0x⟩
      have hq0x' : j q0 = x := by simpa only [j, ha] using hq0x
      obtain ⟨W, _hW, _hqW, _hWt, _hWs, _hcoord,
        O, hO, hqO, _hcollar, _havoid, _hOW, hlocal⟩ :=
        S.exists_morse_rest_old_seam_neighborhood i F rho hrho hsource'
          a ha (havoid a) q0 hq0
      refine ⟨O, hO, hq0x' ▸ hqO, ?_⟩
      intro p hp hpr
      exact ((hlocal p hp (hsurface p hpr)).1).mp hpr
    · exact hy

end PoincareConjecture.M25.Topology3D
