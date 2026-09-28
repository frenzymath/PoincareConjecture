import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityStraightening
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerReconstruction
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLinearChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Boundary

set_option maxHeartbeats 1200000 in

theorem exists_bounded_boundary_target_chart {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e)
    (C : ℝ → M) (hC : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ C)
    (s : ℝ) (hregular : curveVelocity (n := 3) C s ≠ 0) :
    ∃ (j : Fin 3) (H : EuclideanSpace ℝ (Fin N) → LoopAmbient)
      (A : LoopAmbient → M) (L : NNReal) (ρ δ η K : ℝ),
      0 < ρ ∧ 0 < δ ∧ 0 < η ∧ 0 < K ∧ H (e (C s)) = 0 ∧ A 0 = C s ∧
      ContDiff ℝ 1 H ∧ LipschitzWith L H ∧ (∀ y, ‖fderiv ℝ H y‖ ≤ K) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) 1 A (ball 0 (2 * ρ)) ∧
      (∀ y ∈ closedBall (0 : LoopAmbient) ρ, ‖fderiv ℝ (e ∘ A) y‖ ≤ K) ∧
      (∀ q : M, dist (e q) (e (C s)) < δ →
        ‖H (e q)‖ < ρ / 4 ∧ A (H (e q)) = q) ∧
      ∀ t ∈ Ioo (s - η) (s + η),
        H (e (C t)) = (t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j ∧
        A ((t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j) = C t := by
  obtain ⟨T, P, hP0, hP, hPinv⟩ := m65Embedding_exists_linear_chart e he hinj (C s)
  let c := fun t : ℝ => T (e (C t) - e (C s))
  have hc : ContDiff ℝ ∞ c :=
    T.contDiff.comp ((he.comp hC).contDiff.sub contDiff_const)
  have hcs : c s = 0 := by simp [c]
  have hPC : (P ∘ c) =ᶠ[𝓝 s] C := hC.continuous.continuousAt.eventually hPinv
  have hcne : deriv c s ≠ 0 := by
    intro hz
    apply hregular
    have hPcs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ P (c s) := hcs.symm ▸ hP
    have hh := congrArg (fun L : ℝ →L[ℝ] LoopAmbient => L 1)
      (mfderiv_comp s (hPcs.mdifferentiableAt (by simp))
        (hc.contMDiff.contMDiffAt.mdifferentiableAt (by simp)))
    rw [hPC.mfderiv_eq] at hh
    rw [mfderiv_eq_fderiv] at hh
    change curveVelocity C s =
      mfderiv (𝓡 3) (𝓡 3) P (c s) ((fderiv ℝ c s) 1) at hh
    rwa [fderiv_apply_one_eq_deriv, hz, map_zero] at hh
  obtain ⟨j, J, E, hJ, hsJ, _, hcsource, hE0, hmap, hE, hEsymm, haxis, _⟩ :=
    exists_boundary_arc_straightening isOpen_univ (mem_univ s) hc.contDiffOn hcne
  have hsrc : (0 : LoopAmbient) ∈ E.source := hcs ▸ hcsource
  have hEzero : E (0 : LoopAmbient) = 0 := by
    have h := haxis s hsJ
    simpa only [hcs, sub_self, zero_smul] using h
  have hEszero : E.symm (0 : LoopAmbient) = 0 := by
    simpa only [hEzero] using E.left_inv hsrc
  let coordinate := fun y : EuclideanSpace ℝ (Fin N) => E (T (y - e (C s)))
  have hcoord : ContDiffAt ℝ 1 coordinate (e (C s)) := by
    have hEAt : ContDiffAt ℝ ∞ E (T (e (C s) - e (C s))) := by
      simpa only [sub_self, map_zero] using (hE.contDiffAt (E.open_source.mem_nhds hsrc))
    exact (hEAt.comp (e (C s))
      (T.contDiff.contDiffAt.comp (e (C s)) (contDiffAt_id.sub contDiffAt_const))).of_le
        (by simp)
  obtain ⟨H, L, hH, hHD, hHeq⟩ := M65Euler.exists_bounded_extension hcoord
  have hLip : LipschitzWith L H := lipschitzWith_of_nnnorm_fderiv_le
    (hH.differentiable one_ne_zero) (fun y => by exact_mod_cast hHD y)
  have hH0 : H (e (C s)) = 0 := by
    rw [hHeq.self_of_nhds]
    simpa only [coordinate, sub_self, map_zero] using hEzero
  let A := P ∘ E.symm
  have hA0 : A 0 = C s := by simp only [A, Function.comp_apply, hEszero, hP0]
  have hA : ContMDiffAt (𝓡 3) (𝓡 3) ∞ A 0 := by
    have hPs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ P (E.symm 0) := hEszero.symm ▸ hP
    exact hPs.comp 0 (hEsymm.contDiffAt (E.open_target.mem_nhds hE0)).contMDiffAt
  obtain ⟨W, hW, hAW⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp (hA.of_le (by simp : 1 ≤ ∞))
  have heA : ContDiffAt ℝ ∞ (e ∘ A) 0 :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp 0 hA)
  let K0 := ‖fderiv ℝ (e ∘ A) 0‖ + 1
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  have hKn : ∀ᶠ y in 𝓝 (0 : LoopAmbient), ‖fderiv ℝ (e ∘ A) y‖ < K0 :=
    ((heA.fderiv_right (m := 0) (by simp)).continuousAt.norm).eventually
      (Iio_mem_nhds (by dsimp only [K0]; linarith))
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp (inter_mem hW hKn)
  let ρ := r / 3
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hAOn : ContMDiffOn (𝓡 3) (𝓡 3) 1 A (ball 0 (2 * ρ)) :=
    hAW.mono (fun y hy => (hrW (ball_subset_ball
      (show 2 * ρ ≤ r by dsimp only [ρ]; linarith) hy)).1)
  have hAD (y : LoopAmbient) (hy : y ∈ closedBall 0 ρ) :
      ‖fderiv ℝ (e ∘ A) y‖ ≤ K0 :=
    (hrW ((closedBall_subset_ball (by dsimp only [ρ]; linarith)) hy)).2.le
  have hTcont : Continuous (fun q : M => T (e q - e (C s))) :=
    T.continuous.comp (he.continuous.sub continuous_const)
  have hnearE : ∀ᶠ q in 𝓝 (C s), T (e q - e (C s)) ∈ E.source := by
    apply hTcont.continuousAt.preimage_mem_nhds
    simpa only [sub_self, map_zero] using E.open_source.mem_nhds hsrc
  have hinverse : ∀ᶠ q in 𝓝 (C s), A (H (e q)) = q := by
    filter_upwards [he.continuous.continuousAt.eventually hHeq, hPinv, hnearE]
      with q hh hq hsrcq
    rw [hh]
    change P (E.symm (E (T (e q - e (C s))))) = q
    rw [E.left_inv hsrcq, hq]
  have hinverse' : ∀ᶠ y in 𝓝 (e (C s)), ∀ q : M, e q = y → A (H (e q)) = q := by
    rw [hemb.isInducing.nhds_eq_comap (C s), Filter.eventually_comap] at hinverse
    exact hinverse
  have hsmall : ∀ᶠ y in 𝓝 (e (C s)), ‖H y‖ < ρ / 4 := by
    have hh : ‖H (e (C s))‖ < ρ / 4 := by rw [hH0, norm_zero]; positivity
    exact hH.continuous.continuousAt.norm.eventually (Iio_mem_nhds hh)
  obtain ⟨δ, hδ, hδcap⟩ := Metric.mem_nhds_iff.mp (hinverse'.and hsmall)
  have htarget : ∀ᶠ t in 𝓝 s,
      H (e (C t)) = (t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j ∧
        A ((t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j) = C t := by
    filter_upwards [hJ.mem_nhds hsJ, (he.continuous.comp hC.continuous).continuousAt.eventually
      hHeq, hPC] with t ht hHt hPt
    have hXt : E (c t) = (t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j := haxis t ht
    constructor
    · dsimp only [Function.comp_apply] at hHt
      rw [hHt]
      exact hXt
    · rw [← hXt]
      change P (E.symm (E (c t))) = C t
      rw [E.left_inv (hmap ht)]
      exact hPt
  obtain ⟨η, hη, hηcap⟩ := Metric.mem_nhds_iff.mp htarget
  let K := (L : ℝ) + K0 + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨j, H, A, L, ρ, δ, η, K, hρ, hδ, hη, hK, hH0, hA0,
    hH, hLip, ?_, hAOn, ?_, ?_, ?_⟩
  · intro y
    exact (hHD y).trans (by dsimp only [K]; linarith)
  · intro y hy
    exact (hAD y hy).trans (by dsimp only [K]; linarith [L.coe_nonneg])
  · intro q hq
    have hh := hδcap (show e q ∈ ball (e (C s)) δ from hq)
    exact ⟨hh.2, hh.1 q rfl⟩
  · intro t ht
    apply hηcap
    rw [mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

end PoincareConjecture.M65Boundary
