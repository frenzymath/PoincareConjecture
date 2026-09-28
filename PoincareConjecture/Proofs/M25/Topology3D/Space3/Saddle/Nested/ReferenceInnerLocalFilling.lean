import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.MorseChart
import Mathlib.Analysis.Calculus.ContDiff.WithLp









set_option autoImplicit false

open Set Metric
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_inner_reference_local_filling :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let Q : Set E2 := Metric.closedBall 0 (1 / 2)
    ∃ (vmin : E2) (m a : ℝ) (e0 : OpenPartialHomeomorph E2 E2),
      vmin ∈ Metric.ball (0 : E2) (1 / 2) ∧ m = U vmin ∧
      (63 : ℝ) / 64 ≤ m ∧ m ≤ 1 ∧
      (∀ v ∈ Q, fderiv ℝ U v = 0 ↔ v = vmin) ∧
      (∀ v ∈ Q, m + ‖v - vmin‖ ^ 2 / 6 ≤ U v) ∧
      0 < a ∧ m + 9 * a ^ 2 < (17 : ℝ) / 16 + 1 / 8192 ∧
      e0 0 = vmin ∧ Metric.closedBall 0 (3 * a) ⊆ e0.source ∧
      e0.target ⊆ Metric.ball 0 (1 / 2) ∧
      ContDiffOn ℝ ∞ e0 e0.source ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ p ∈ e0.source, U (e0 p) = m + ‖p‖ ^ 2) ∧
      (∀ v ∈ Q, U v ≤ m + 9 * a ^ 2 → v ∈ e0.target) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 3 * a →
        e0 '' Metric.closedBall 0 r = {v : E2 | v ∈ Q ∧ U v ≤ m + r ^ 2} ∧
        e0 '' Metric.ball 0 r = {v : E2 | v ∈ Q ∧ U v < m + r ^ 2} ∧
        e0 '' Metric.sphere 0 r = {v : E2 | v ∈ Q ∧ U v = m + r ^ 2}) := by
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let Q : Set E2 := closedBall 0 (1 / 2)
  obtain ⟨hsmooth, _hstrict, _hHessian, _hbound, _hboundary, _htangent,
    vmin, hvmin, hlo, hhi, hcritical, hunique, hinj, hgap, _hsublevels⟩ :=
      inner_reference_convex_geometry
  let m := U vmin
  change ContDiffOn ℝ ∞ U (ball (0 : E2) 1) at hsmooth
  change ∀ v ∈ Q, m + ‖v - vmin‖ ^ 2 / 6 ≤ U v at hgap
  have hDunit : ball (0 : E2) (1 / 2) ⊆ ball (0 : E2) 1 := by
    intro v hv
    rw [mem_ball_zero_iff] at hv ⊢
    linarith only [hv]
  obtain ⟨sigma, tau, eM, hsigma, htau, hvmS, hMS, hMzero, hM, hMi, hMform⟩ :=
    exists_morse_chart (finrank_euclideanSpace_fin (n := 2)) U isOpen_ball
      (hsmooth.mono hDunit) vmin hvmin hcritical hinj
  have hmin (v : E2) (hv : v ∈ Q) : m ≤ U v := by
    linarith only [hgap v hv, sq_nonneg ‖v - vmin‖]
  have h0T : (0 : ℝ × ℝ) ∈ eM.target := hMzero ▸ eM.map_source hvmS
  obtain ⟨rho, hrho, hrhoT⟩ := Metric.isOpen_iff.mp eM.open_target 0 h0T
  have haxis0 : (rho / 2, (0 : ℝ)) ∈ eM.target := by
    apply hrhoT
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_zero, abs_of_pos (by linarith only [hrho])]
    constructor <;> linarith only [hrho]
  have haxis1 : ((0 : ℝ), rho / 2) ∈ eM.target := by
    apply hrhoT
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_zero, abs_of_pos (by linarith only [hrho])]
    constructor <;> linarith only [hrho]
  have hsign0 : sigma = 1 := by
    have hf := hMform (eM.symm (rho / 2, 0)) (eM.map_target haxis0)
    rw [eM.right_inv haxis0] at hf
    have hm := hmin (eM.symm (rho / 2, 0))
      (ball_subset_closedBall (hMS (eM.map_target haxis0)))
    change U (eM.symm (rho / 2, 0)) = m + sigma * (rho / 2) ^ 2 + tau * 0 ^ 2 at hf
    have hs : sigma = 1 ∨ sigma = -1 := mul_self_eq_one_iff.mp hsigma
    rcases hs with hs | hs
    · exact hs
    · rw [hs] at hf
      nlinarith only [hf, hm, hrho]
  have hsign1 : tau = 1 := by
    have hf := hMform (eM.symm (0, rho / 2)) (eM.map_target haxis1)
    rw [eM.right_inv haxis1] at hf
    have hm := hmin (eM.symm (0, rho / 2))
      (ball_subset_closedBall (hMS (eM.map_target haxis1)))
    change U (eM.symm (0, rho / 2)) = m + sigma * 0 ^ 2 + tau * (rho / 2) ^ 2 at hf
    have hs : tau = 1 ∨ tau = -1 := mul_self_eq_one_iff.mp htau
    rcases hs with hs | hs
    · exact hs
    · rw [hs] at hf
      nlinarith only [hf, hm, hrho]
  let P : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let e0 : OpenPartialHomeomorph E2 E2 :=
    P.toHomeomorph.transOpenPartialHomeomorph eM.symm
  have hsource : e0.source = P ⁻¹' eM.target := rfl
  have htarget : e0.target = eM.source := rfl
  have h0S : (0 : E2) ∈ e0.source := by
    change P 0 ∈ eM.target
    simpa only [map_zero] using h0T
  have hzero : e0 0 = vmin := by
    change eM.symm (P 0) = vmin
    rw [map_zero, ← hMzero, eM.left_inv hvmS]
  have hvmT : vmin ∈ e0.target := hvmS
  have htargetD : e0.target ⊆ ball (0 : E2) (1 / 2) := hMS
  have he0 : ContDiffOn ℝ ∞ e0 e0.source :=
    hMi.comp P.contDiff.contDiffOn (fun _ hx => hx)
  have he0i : ContDiffOn ℝ ∞ e0.symm e0.target :=
    P.symm.contDiff.comp_contDiffOn hM
  have hquad (p : E2) (hp : p ∈ e0.source) : U (e0 p) = m + ‖p‖ ^ 2 := by
    change P p ∈ eM.target at hp
    have hnorm : ‖p‖ ^ 2 = (P p).1 ^ 2 + (P p).2 ^ 2 := by
      change ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2
      simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
    have hf := hMform (eM.symm (P p)) (eM.map_target hp)
    rw [eM.right_inv hp, hsign0, hsign1, one_mul, one_mul] at hf
    change U (eM.symm (P p)) = m + ‖p‖ ^ 2
    rw [hnorm]
    dsimp only [m]
    linarith only [hf]
  obtain ⟨eps, heps, hepsT⟩ := Metric.isOpen_iff.mp e0.open_target vmin hvmT
  obtain ⟨eta, heta, hetaS⟩ := Metric.isOpen_iff.mp e0.open_source 0 h0S
  let B : ℝ := 17 / 16 + 1 / 8192
  have hmB : 0 < B - m := by
    change U vmin ≤ 1 at hhi
    dsimp only [B, m]
    linarith only [hhi]
  let a : ℝ := min (eta / 6) (min (eps / 12) (Real.sqrt (B - m) / 6))
  have ha : 0 < a := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hae : a ≤ eta / 6 := min_le_left _ _
  have hap : a ≤ eps / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have haB : a ≤ Real.sqrt (B - m) / 6 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsourceRadius : 3 * a < eta := by linarith only [hae, heta]
  have hgapRadius : 54 * a ^ 2 < eps ^ 2 := by nlinarith only [hap, ha, heps]
  have hheight : m + 9 * a ^ 2 < B := by
    have hs0 := Real.sqrt_nonneg (B - m)
    have hs2 := Real.sq_sqrt hmB.le
    have hsq : (6 * a) ^ 2 ≤ (Real.sqrt (B - m)) ^ 2 :=
      (sq_le_sq₀ (by positivity) hs0).mpr (by
        simpa only [mul_comm] using
          (le_div_iff₀ (show (0 : ℝ) < 6 by norm_num)).mp haB)
    nlinarith only [hsq, hs2, hmB]
  have hclosedSource : closedBall (0 : E2) (3 * a) ⊆ e0.source := by
    intro p hp
    exact hetaS (mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hp).trans_lt hsourceRadius))
  have hfull (v : E2) (hv : v ∈ Q) (hval : U v ≤ m + 9 * a ^ 2) :
      v ∈ e0.target := by
    apply hepsT
    rw [mem_ball, dist_eq_norm]
    have hh := hgap v hv
    nlinarith only [hh, hval, hgapRadius, norm_nonneg (v - vmin), heps]
  refine ⟨vmin, m, a, e0, hvmin, rfl, hlo, hhi, hunique, hgap, ha,
    hheight, hzero, hclosedSource, htargetD, he0, he0i, hquad, hfull, ?_⟩
  intro r hr hrA
  change e0 '' closedBall 0 r = {v : E2 | v ∈ Q ∧ U v ≤ m + r ^ 2} ∧
    e0 '' ball 0 r = {v : E2 | v ∈ Q ∧ U v < m + r ^ 2} ∧
    e0 '' sphere 0 r = {v : E2 | v ∈ Q ∧ U v = m + r ^ 2}
  have hr2 : r ^ 2 ≤ 9 * a ^ 2 := by nlinarith only [hr, hrA, ha]
  have hsrc (p : E2) (hp : p ∈ closedBall (0 : E2) r) : p ∈ e0.source :=
    hclosedSource (mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans hrA))
  have himageQ (p : E2) (hp : p ∈ closedBall (0 : E2) r) : e0 p ∈ Q :=
    ball_subset_closedBall (htargetD (e0.map_source (hsrc p hp)))
  have htargetOfLe (v : E2) (hv : v ∈ Q) (hval : U v ≤ m + r ^ 2) : v ∈ e0.target :=
    hfull v hv (hval.trans (by linarith only [hr2]))
  have hinverse (v : E2) (hv : v ∈ e0.target) : U v = m + ‖e0.symm v‖ ^ 2 := by
    simpa only [e0.right_inv hv] using hquad (e0.symm v) (e0.map_target hv)
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨himageQ p hp, ?_⟩
      rw [hquad p (hsrc p hp)]
      have hn := mem_closedBall_zero_iff.mp hp
      nlinarith only [hn, norm_nonneg p, hr]
    · rintro ⟨hv, hval⟩
      have ht := htargetOfLe v hv hval
      refine ⟨e0.symm v, mem_closedBall_zero_iff.mpr ?_, e0.right_inv ht⟩
      nlinarith only [hinverse v ht, hval, norm_nonneg (e0.symm v), hr]
  · ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpc := ball_subset_closedBall hp
      refine ⟨himageQ p hpc, ?_⟩
      rw [hquad p (hsrc p hpc)]
      have hn := mem_ball_zero_iff.mp hp
      nlinarith only [hn, norm_nonneg p, hr]
    · rintro ⟨hv, hval⟩
      have ht := htargetOfLe v hv hval.le
      refine ⟨e0.symm v, mem_ball_zero_iff.mpr ?_, e0.right_inv ht⟩
      nlinarith only [hinverse v ht, hval, norm_nonneg (e0.symm v), hr]
  · ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpc := sphere_subset_closedBall hp
      refine ⟨himageQ p hpc, ?_⟩
      rw [hquad p (hsrc p hpc), mem_sphere_zero_iff_norm.mp hp]
    · rintro ⟨hv, hval⟩
      have ht := htargetOfLe v hv hval.le
      refine ⟨e0.symm v, mem_sphere_zero_iff_norm.mpr ?_, e0.right_inv ht⟩
      nlinarith only [hinverse v ht, hval, norm_nonneg (e0.symm v), hr]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
