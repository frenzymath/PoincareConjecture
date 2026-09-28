import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.morse_disc_middle_geometry
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
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let disc : Set E3 := j '' (F '' closedBall (0 : E2) rho)
    let discOpen : Set E3 := j '' (F '' ball (0 : E2) rho)
    let seam : Set E3 := j '' (F '' sphere (0 : E2) rho)
    let s : ℝ := c + kappa * rho ^ 2
    let z0 : ℝ := c + 2 * kappa * rho ^ 2
    IsCompact disc ∧ IsCompact seam ∧ IsConnected seam ∧
      disc \ discOpen = seam ∧
      |z0 - c| < D ∧ 0 < kappa * (z0 - s) ∧
      (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
        (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal < z0) ∧
      (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
        z0 < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) ∧
      (∀ y ∈ disc,
        0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - c) ∧
        kappa * (⟪(u : E3), y⟫_ℝ - c) ≤ rho ^ 2 ∧
        kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ 0 ∧
        (⟪(u : E3), y⟫_ℝ = s ↔ y ∈ seam) ∧
        (kappa * (⟪(u : E3), y⟫_ℝ - s) < 0 ↔ y ∉ seam)) ∧
      ∀ y ∈ disc, ⟪(u : E3), y⟫_ℝ ≠ z0 := by
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let s : ℝ := c + kappa * rho ^ 2
  let z0 : ℝ := c + 2 * kappa * rho ^ 2
  have hj : Continuous j := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hjinj : Function.Injective j := by
    intro q q' hqq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hqq)
  obtain ⟨_hzero, _hopenDisc, _htarget, _hopen, hdisc, hseam, hconn,
    _hclosure, hdiff, _hfrontier⟩ := nativeDiscChart_geometry F rho hrho hsource
  have hkap2 : kappa ^ 2 = 1 := by nlinarith only [sq_abs kappa, hkappa]
  have hkap : kappa ≠ 0 := by
    intro h
    rw [h, abs_zero] at hkappa
    norm_num at hkappa
  have hzabs : |z0 - c| = 2 * rho ^ 2 := by
    calc
      |z0 - c| = |2 * kappa * rho ^ 2| := by dsimp only [z0]; congr 1; ring
      _ = 2 * rho ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          hkappa, abs_of_nonneg (sq_nonneg rho)]
        ring
  have hzsmall : |z0 - c| < D := by rwa [hzabs]
  have hzside : 0 < kappa * (z0 - s) := by
    have he : kappa * (z0 - s) = rho ^ 2 := by
      calc
        _ = kappa ^ 2 * rho ^ 2 := by dsimp only [z0, s]; ring
        _ = rho ^ 2 := by rw [hkap2, one_mul]
    rw [he]
    exact sq_pos_of_pos hrho
  have hfull (y : E3) (hy : y ∈ j '' (F '' closedBall (0 : E2) rho)) :
      0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - c) ∧
      kappa * (⟪(u : E3), y⟫_ℝ - c) ≤ rho ^ 2 ∧
      kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ 0 ∧
      (⟪(u : E3), y⟫_ℝ = s ↔ y ∈ j '' (F '' sphere (0 : E2) rho)) ∧
      (kappa * (⟪(u : E3), y⟫_ℝ - s) < 0 ↔
        y ∉ j '' (F '' sphere (0 : E2) rho)) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
    have hnorm : ‖x‖ ^ 2 ≤ rho ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) hrho.le).mpr (mem_closedBall_zero_iff.mp hx)
    have hsigned : kappa * (⟪(u : E3), j (F x)⟫_ℝ - c) = ‖x‖ ^ 2 := by
      change kappa * (⟪(u : E3), psi i (F x, 0)⟫_ℝ - c) = ‖x‖ ^ 2
      rw [hform x hx]
      calc
        _ = kappa ^ 2 * ‖x‖ ^ 2 := by ring
        _ = ‖x‖ ^ 2 := by rw [hkap2, one_mul]
    have hrelative : kappa * (⟪(u : E3), j (F x)⟫_ℝ - s) =
        ‖x‖ ^ 2 - rho ^ 2 := by
      calc
        _ = kappa * (⟪(u : E3), j (F x)⟫_ℝ - c) - kappa ^ 2 * rho ^ 2 := by
          dsimp only [s]
          ring
        _ = ‖x‖ ^ 2 - rho ^ 2 := by rw [hsigned, hkap2, one_mul]
    have hside : kappa * (⟪(u : E3), j (F x)⟫_ℝ - s) ≤ 0 := by
      rw [hrelative]
      linarith only [hnorm]
    have hboundary : ⟪(u : E3), j (F x)⟫_ℝ = s ↔
        j (F x) ∈ j '' (F '' sphere (0 : E2) rho) := by
      constructor
      · intro hh
        have hxnorm : ‖x‖ = rho := by
          rw [hh, sub_self, mul_zero] at hrelative
          nlinarith only [hrelative, norm_nonneg x, hrho]
        exact ⟨F x, ⟨x, mem_sphere_zero_iff_norm.mpr hxnorm, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, hv, rfl⟩, heq⟩
        rw [← heq]
        change ⟪(u : E3), psi i (F v, 0)⟫_ℝ = c + kappa * rho ^ 2
        rw [hform v (sphere_subset_closedBall hv), mem_sphere_zero_iff_norm.mp hv]
    refine ⟨by rw [hsigned]; exact sq_nonneg ‖x‖,
      by rw [hsigned]; exact hnorm, hside, hboundary, ?_⟩
    constructor
    · intro hlt hmem
      rw [hboundary.mpr hmem, sub_self, mul_zero] at hlt
      exact (lt_irrefl 0) hlt
    · intro hnot
      apply lt_of_le_of_ne hside
      intro heq
      apply hnot
      apply hboundary.mp
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hkap)
  refine ⟨hdisc.image hj, hseam.image hj, hconn.image j hj.continuousOn,
    ?_, hzsmall, hzside, ?_, ?_, hfull, ?_⟩
  · rw [← image_sdiff hjinj, hdiff]
  · intro a hai has
    have hl := hlower a hai has
    have hz := (abs_lt.mp hzsmall).1
    linarith only [hl, hz, S.buffer_pos]
  · intro a hai has
    have hu := hupper a hai has
    have hz := (abs_lt.mp hzsmall).2
    linarith only [hu, hz, S.buffer_pos]
  · intro y hy hh
    have hb := (hfull y hy).2.2.1
    rw [hh] at hb
    exact (not_lt_of_ge hb) hzside

end PoincareConjecture.M25.Topology3D
