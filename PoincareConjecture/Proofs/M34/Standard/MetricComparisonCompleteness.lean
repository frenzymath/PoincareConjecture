import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

@[instance_reducible] noncomputable def comparisonPseudoEMetric (g : RiemannianMetric n M) :
    PseudoEMetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  (EMetricSpace.ofRiemannianMetric (𝓡 n) M).toPseudoEMetricSpace

theorem comparisonPseudoEMetric_topology (g : RiemannianMetric n M) :
    g.comparisonPseudoEMetric.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M) := rfl

theorem comparisonPseudoEMetric_edist (g : RiemannianMetric n M) (x y : M) :
    g.comparisonPseudoEMetric.edist x y = g.edist x y := rfl

theorem metricComplete_iff_comparisonPseudoEMetric (g : RiemannianMetric n M) :
    MetricComplete g ↔ @CompleteSpace M g.comparisonPseudoEMetric.toUniformSpace := Iff.rfl

theorem metricComplete_of_tangentNorm_comparison
    [PreconnectedSpace M] (g h : RiemannianMetric n M) (p : M)
    (hg : MetricComplete g) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x), g.tangentNorm x v ≤ C * h.tangentNorm x v) :
    MetricComplete h := by
  rw [metricComplete_iff_comparisonPseudoEMetric] at hg ⊢
  apply Poincare.completeSpace_of_continuous_local_edist_bound
    g.comparisonPseudoEMetric h.comparisonPseudoEMetric p hg
  · rw [comparisonPseudoEMetric_topology, comparisonPseudoEMetric_topology]
    exact continuous_id
  · have hpc : @PreconnectedSpace M
        h.comparisonPseudoEMetric.toUniformSpace.toTopologicalSpace := by
      rw [comparisonPseudoEMetric_topology]
      infer_instance
    exact fun x => @Poincare.edist_ne_top_of_preconnected M h.comparisonPseudoEMetric hpc x p
  · intro R
    let r : ℝ := R + 1
    have hr : 0 < r := by dsimp [r]; positivity
    have hR : (R : ℝ≥0∞) < ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by dsimp [r]; linarith)
    have hmem (z : M) (hz : h.comparisonPseudoEMetric.edist z p ≤ R) :
        z ∈ h.ball p r := by
      change h.edist p z < ENNReal.ofReal r
      rw [← comparisonPseudoEMetric_edist, h.comparisonPseudoEMetric.edist_comm]
      exact hz.trans_lt hR
    refine ⟨Real.toNNReal C, fun x y hx hy => ?_⟩
    rw [comparisonPseudoEMetric_edist, comparisonPseudoEMetric_edist]
    change g.edist x y ≤ ENNReal.ofReal C * h.edist x y
    exact edist_le_mul_edist_of_tangentNorm_le_on_ball h g p r C hr hC
      (fun z _ v => hbound z v) (hmem x hx) (hmem y hy)

end PoincareConjecture.RiemannianMetric
