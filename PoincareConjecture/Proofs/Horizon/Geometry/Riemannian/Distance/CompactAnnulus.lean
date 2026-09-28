import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic


set_option autoImplicit false
open Set
open scoped Manifold ContDiff
namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isCompact_real_distance_annulus (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (a b : ℝ) :
    IsCompact {y : M | a ≤ (g.edist p y).toReal ∧ (g.edist p y).toReal ≤ b} := by
  apply (g.isCompact_closedBall_of_metricComplete hc p b).of_isClosed_subset
  · exact (isClosed_le continuous_const (g.continuous_toReal_edist p)).inter
      (isClosed_le (g.continuous_toReal_edist p) continuous_const)
  · intro y hy
    exact (ENNReal.ofReal_toReal (g.edist_ne_top p y)).symm.le.trans
      (ENNReal.ofReal_le_ofReal hy.2)

theorem isCompact_commonLevel_distance_annulus (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (a b : ℝ)
    {ι : Type*} (f : ι → M → ℝ) (hf : ∀ i, Continuous (f i)) (v : ι → ℝ) :
    IsCompact {y : M | (a ≤ (g.edist p y).toReal ∧ (g.edist p y).toReal ≤ b) ∧
      ∀ i, f i y = v i} := by
  have hclosed : IsClosed {y : M | ∀ i, f i y = v i} := by
    simpa only [ofPred_forall] using
      (isClosed_iInter fun i => isClosed_eq (hf i) (continuous_const (y := v i)))
  exact (g.isCompact_real_distance_annulus hc p a b).inter_right hclosed

end PoincareConjecture.RiemannianMetric
