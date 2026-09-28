import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Compactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_uniform_positive_neighborhood_of_normalized_ancient_limit
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (F : ℕ → RicciFlow n M (Iic 0))
    (hRic : ∀ k t, t ≤ 0 → ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ ((F k).connection t).ricci x v v)
    (Φ : ℕ → EuclideanSpace ℝ (Fin n) → M)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hzero : 0 ∈ U)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hconv : ∀ t ≤ 0, ∀ x ∈ U, Tendsto
      (fun k => ((F k).metric t).pullbackCoefficients (Φ k) x) atTop (𝓝 (B (t, x))))
    (hcont : ContinuousAt (fun x => B (0, x)) 0)
    (hnorm : ∀ v w, B (0, 0) v w = inner ℝ v w) :
    (∀ t ≤ 0, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v) ∧
    (∀ x ∈ U, ∀ v, AntitoneOn (fun t => B (t, x) v v) (Iic 0)) ∧
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
      ∀ t ≤ 0, ∀ x ∈ V, ∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B (t, x) v v := by
  have heval (t : ℝ) (ht : t ≤ 0) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (v w : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => ((F k).metric t).pullbackCoefficients (Φ k) x v w)
        atTop (𝓝 (B (t, x) v w)) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto _).comp (hconv t ht x hx))
  have hsymm : ∀ t ≤ 0, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v := by
    intro t ht x hx v w
    exact tendsto_nhds_unique (heval t ht x hx v w)
      ((heval t ht x hx w v).congr (fun k => ((F k).metric t).symm (Φ k x) _ _))
  have hmono : ∀ x ∈ U, ∀ v, AntitoneOn (fun t => B (t, x) v v) (Iic 0) := by
    intro x hx v s hs t ht hst
    apply le_of_tendsto_of_tendsto (heval t ht x hx v v) (heval s hs x hx v v)
    apply Eventually.of_forall
    intro k
    exact (F k).antitoneOn_metric_inner_self_on_ancient_of_ricci_nonneg
      (Φ k x) (mfderiv (𝓡 n) (𝓡 n) (Φ k) x v)
      (fun r hr => hRic k r hr _ _) hs ht hst
  have hclose : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ‖B (0, x) - B (0, 0)‖ < 1 / 2 := by
    have hc := hcont.eventually
      (Metric.ball_mem_nhds (B (0, 0)) (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [Metric.mem_ball, dist_eq_norm] using hc
  obtain ⟨V, hV, hVo, hzeroV⟩ :=
    mem_nhds_iff.mp (inter_mem (hU.mem_nhds hzero) hclose)
  have hVU : V ⊆ U := fun x hx => (hV hx).1
  refine ⟨hsymm, hmono, V, hVo, hzeroV, hVU, fun t ht x hx v => ?_⟩
  have hbound := ((B (0, x) - B (0, 0)) v).le_opNorm v
  have hbound' := (B (0, x) - B (0, 0)).le_opNorm v
  have habs : |B (0, x) v v - ‖v‖ ^ 2| ≤
      ‖B (0, x) - B (0, 0)‖ * ‖v‖ ^ 2 := by
    have h := hbound.trans (mul_le_mul_of_nonneg_right hbound' (norm_nonneg v))
    simpa only [sub_apply, hnorm, real_inner_self_eq_norm_sq,
      Real.norm_eq_abs, mul_assoc, ← sq] using h
  have hsmall := mul_le_mul_of_nonneg_right (hV hx).2.le (sq_nonneg ‖v‖)
  have hlow := (abs_le.mp habs).1
  have hterminal : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B (0, x) v v := by nlinarith
  exact hterminal.trans (hmono x (hVU hx) v ht (by simp) ht)

end PoincareConjecture.RicciFlow
