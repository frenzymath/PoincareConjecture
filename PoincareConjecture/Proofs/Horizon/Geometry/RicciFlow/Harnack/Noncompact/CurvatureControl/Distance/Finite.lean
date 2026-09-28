import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_minimizing_geodesic_of_metricComplete_of_finite
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {p x : M} (hfinite : g.edist p x ≠ ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧
      γ 0 = p ∧ γ 1 = x ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p x := by
  let R := (g.edist p x).toReal + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  apply g.exists_minimizing_geodesic_of_precompact_ball p x hR
    (g.isCompact_closure_ball_of_metricComplete hc p R)
  change g.edist p x < ENNReal.ofReal R
  rw [← ENNReal.ofReal_toReal hfinite]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by
    dsimp [R]
    linarith)

theorem continuousAt_toReal_edist_of_ne_top
    (g : RiemannianMetric n M) (O y : M)
    (hfinite : g.edist O y ≠ ⊤) :
    ContinuousAt (fun z => (g.edist O z).toReal) y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact (ENNReal.continuousAt_toReal hfinite).comp
    (continuous_const.edist continuous_id).continuousAt

end PoincareConjecture.RiemannianMetric
