import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerReconstruction
import Mathlib.Analysis.Calculus.MeanValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Euler




theorem exists_bounded_chart_extension {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (p : M) :
    ∃ (H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 3)) (C : NNReal),
      ContDiff ℝ 1 H ∧ (∀ y, ‖fderiv ℝ H y‖ ≤ (C : ℝ)) ∧
        LipschitzWith C H ∧ ∀ᶠ q in 𝓝 p, H (e q) = extChartAt (𝓡 3) p q := by
  let c := extChartAt (𝓡 3) p
  obtain ⟨L, P, hP0, hP, hPinv⟩ := m65Embedding_exists_linear_chart e he hinj p
  have hcP : ContDiffAt ℝ ∞ (fun y => c (P y)) 0 := by
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c (P 0) :=
      hP0.symm ▸ (contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞))
    exact contMDiffAt_iff_contDiffAt.mp (hc.comp 0 hP)
  have hlin : ContDiffAt ℝ ∞ (fun y => L (y - e p)) (e p) :=
    L.contDiff.contDiffAt.comp (e p) (contDiffAt_id.sub contDiffAt_const)
  have hh : ContDiffAt ℝ 1 (fun y => c (P (L (y - e p)))) (e p) := by
    have hcp' : ContDiffAt ℝ ∞ (fun y => c (P y)) (L (e p - e p)) := by
      simpa only [sub_self, map_zero] using hcP
    exact (ContDiffAt.comp (f := fun y => L (y - e p))
      (g := fun y => c (P y)) (e p) hcp' hlin).of_le (by simp)
  obtain ⟨H, C, hH, hC, hHeq⟩ := exists_bounded_extension hh
  have hLip : LipschitzWith C H := lipschitzWith_of_nnnorm_fderiv_le
    (hH.differentiable one_ne_zero) (fun y => by exact_mod_cast hC y)
  refine ⟨H, C, hH, hC, hLip, ?_⟩
  filter_upwards [he.continuous.continuousAt.eventually hHeq, hPinv] with q hHq hPq
  rw [hHq, hPq]

set_option maxHeartbeats 1600000 in





theorem exists_chart_field_transfer {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    {U V : Set LoopPlane} (hU : IsOpen U) (hV : IsOpen V)
    (F : M65LocalWeakMap e U)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) V)
    (q : LoopPlane → M) (hqcont : ContinuousOn q U)
    (hq : q =ᵐ[volume.restrict U] F.value) {x : LoopPlane} (hxU : x ∈ U) (hxV : x ∈ V)
    (hX : ∀ z ∈ V, X.value z = extChartAt (𝓡 3) (q x) (q z)) :
    ∃ r : ℝ, 0 < r ∧ closedBall x (4 * r) ⊆ U ∩ V ∧
      ∃ (H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 3)) (C : NNReal),
        ContDiff ℝ 1 H ∧ (∀ y, ‖fderiv ℝ H y‖ ≤ (C : ℝ)) ∧ LipschitzWith C H ∧
        (∀ z ∈ ball x (2 * r), X.value z = H (e (q z))) ∧
        ∀ i, X.derivative i =ᵐ[volume.restrict (ball x (2 * r))] fun z =>
          fderiv ℝ H (e (q z)) (F.derivative i z) := by
  obtain ⟨H, C, hH, hC, hLip, hcap⟩ := exists_bounded_chart_extension e he hinj (q x)
  have hqc := hqcont.continuousAt (hU.mem_nhds hxU)
  have hnear : ∀ᶠ z in 𝓝 x,
      z ∈ U ∩ V ∧ H (e (q z)) = extChartAt (𝓡 3) (q x) (q z) :=
    Filter.Eventually.and ((hU.inter hV).mem_nhds ⟨hxU, hxV⟩) (hqc.eventually hcap)
  obtain ⟨η, hη, hηcap⟩ := Metric.mem_nhds_iff.mp hnear
  let r := η / 8
  have hr : 0 < r := by dsimp only [r]; positivity
  have h4η : closedBall x (4 * r) ⊆ ball x η :=
    closedBall_subset_ball (by dsimp only [r]; linarith)
  have h4sub : closedBall x (4 * r) ⊆ U ∩ V := fun z hz => (hηcap (h4η hz)).1
  have h24 : closedBall x (2 * r) ⊆ closedBall x (4 * r) :=
    closedBall_subset_closedBall (by linarith)
  have h2U : closedBall x (2 * r) ⊆ U := (h24.trans h4sub).trans inter_subset_left
  have h2V : ball x (2 * r) ⊆ V :=
    (ball_subset_closedBall.trans (h24.trans h4sub)).trans inter_subset_right
  have hvalue (z : LoopPlane) (hz : z ∈ ball x (2 * r)) : X.value z = H (e (q z)) :=
    (hX z (h2V hz)).trans (hηcap (h4η (h24 (ball_subset_closedBall hz)))).2.symm
  let Fq := replace_value F q (hq.mono (fun _ hz => congrArg e hz))
  let Y := compose_on_ball Fq hU x (show 0 ≤ 2 * r by positivity) h2U H hH C hC
  let Xsmall := restrict_map X h2V
  have heq : (fun z => (fun y : EuclideanSpace ℝ (Fin 3) => y) (Xsmall.value z))
      =ᵐ[volume.restrict (ball x (2 * r))] Y.value := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hvalue z hz
  refine ⟨r, hr, h4sub, H, C, hH, hC, hLip, hvalue, ?_⟩
  intro i
  exact derivative_unique isOpen_ball Xsmall Y heq i

end PoincareConjecture.M65Euler
