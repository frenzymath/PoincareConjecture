import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_short_segment (g : RiemannianMetric n M) (hc : MetricComplete g)
    (p q : M) {r : ℝ} (hr : 0 < r) (hq : q ∈ g.ball p r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-ε) (1 + ε)) ∧
      γ 0 = p ∧ γ 1 = q ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ g.ball p r) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = (g.edist p q).toReal ^ 2) := by
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball p q hr
      (g.isCompact_closure_ball_of_metricComplete hc p r) hq
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have h0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at h0 p (by
    simpa only [hγ0] using mem_extChartAt_source p)).1
  have hC0 : g.tangentNorm p (deriv (fun s ↦ extChartAt (𝓡 n) p (γ s)) 0) = C := by
    simpa only [chartCoefficients_self, tangentNorm] using
      (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
  have hCL : (C : ℝ) = (g.edist p q).toReal := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at h
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C : ℝ) from C.2)] using
      congrArg ENNReal.toReal h
  refine ⟨ε, hε, γ, (fun s hs ↦
    (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ hs).contMDiffWithinAt),
      hγ0, hγ1, ?_, ?_⟩
  · intro s hs
    have hd := hmin 0 (by simp) s hs
    rw [hγ0, zero_sub, abs_neg, abs_of_nonneg hs.1] at hd
    change g.edist p (γ s) < ENNReal.ofReal r
    rw [hd]
    apply lt_of_le_of_lt _ hq
    exact mul_le_of_le_one_left' (by simpa using ENNReal.ofReal_le_ofReal hs.2)
  · intro s hs
    have hnonneg : 0 ≤ g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) := by
      by_cases hz : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1 = 0
      · simp [hz]
      · exact (g.pos (γ s) _ hz).le
    have hsq := congrArg (fun a : ℝ ↦ a ^ 2) (hC s (hI hs))
    rw [tangentNorm, Real.sq_sqrt hnonneg, hCL] at hsq
    exact hsq

end PoincareConjecture.RiemannianMetric
