import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]


lemma exists_heat_harnack_path (g : RiemannianMetric n M) (hc : MetricComplete g)
    (O x y : M) {R : ℝ}
    (hx : (g.edist O x).toReal ≤ R) (hy : (g.edist O y).toReal ≤ R) :
    ∃ γ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc 0 1) ∧
      γ 0 = x ∧ γ 1 = y ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (g.edist O (γ s)).toReal ≤ 3 * R) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = (g.edist x y).toReal ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let L := (g.edist x y).toReal
  have hcompact : IsCompact (closure (g.ball x (L + 1))) := by
    apply (g.isCompact_closedBall_of_metricComplete hc x (L + 1)).of_isClosed_subset
      isClosed_closure
    apply closure_minimal (fun z (h : g.edist x z < ENNReal.ofReal (L + 1)) => h.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hL : 0 < L + 1 := by dsimp [L]; positivity
  have hxy : y ∈ g.ball x (L + 1) := by
    change g.edist x y < ENNReal.ofReal (L + 1)
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top x y)]
    exact (ENNReal.ofReal_lt_ofReal_iff hL).mpr (by dsimp [L]; linarith)
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball x y hL hcompact hxy
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have h0 := hI (show (0 : ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at h0 x (by
    simpa only [hγ0] using mem_extChartAt_source x)).1
  have hC0 : g.tangentNorm x (deriv (fun s => extChartAt (𝓡 n) x (γ s)) 0) = C := by
    simpa only [chartCoefficients_self, tangentNorm] using
      (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
  have hCL : (C : ℝ) = L := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at h
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C : ℝ) from C.2)] using
      congrArg ENNReal.toReal h
  refine ⟨γ, hγ.contMDiffOn.mono hI, hγ0, hγ1, ?_, ?_⟩
  · intro s hs
    have hxs := congrArg ENNReal.toReal (hmin 0 (by simp) s hs)
    rw [hγ0, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      zero_sub, abs_neg, abs_of_nonneg hs.1] at hxs
    have hdxy : L ≤ 2 * R := by
      have htri := g.toReal_edist_triangle x O y
      have hsym : g.edist x O = g.edist O x := edist_comm x O
      rw [hsym] at htri
      dsimp [L]
      linarith
    have htri := g.toReal_edist_triangle O x (γ s)
    rw [hxs] at htri
    have hLs : s * L ≤ L := mul_le_of_le_one_left ENNReal.toReal_nonneg hs.2
    dsimp only [L] at hLs hdxy
    linarith
  · intro s hs
    have hvnonneg : 0 ≤ g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) := by
      change 0 ≤ inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      exact real_inner_self_nonneg
    have hh := hC s (hI hs)
    rw [hCL] at hh
    have hsq := congrArg (fun r : ℝ => r ^ 2) hh
    rw [tangentNorm, Real.sq_sqrt hvnonneg] at hsq
    exact hsq

end PoincareConjecture.RiemannianMetric
