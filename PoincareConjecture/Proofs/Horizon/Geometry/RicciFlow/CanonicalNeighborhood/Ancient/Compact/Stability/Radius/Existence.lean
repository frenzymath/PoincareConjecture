import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [ConnectedSpace M]

theorem exists_unique_scalar_core_radius (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) (p : M) :
    ∃! r : ℝ, 0 < r ∧ scalarCurvatureSupOn g D (g.ball p r) = r⁻¹ ^ 2 := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  have hclosure (x : M) (r : ℝ) (hr : 0 < r) :
      closure (Metric.ball x r) = Metric.closedBall x r :=
    CompactKappaCoreRadius.closure_ball_eq_of_approximate_split
      (fun x y _ _ hr hε ↦ g.approximate_split_toMetricSpace x y hr hε) x hr
  have hsup (r : ℝ) : scalarCurvatureSupOn g D (g.ball p r) =
      sSup (D.scalarCurvature '' Metric.ball p r) := by
    rw [g.toMetricSpace_ball]
    unfold scalarCurvatureSupOn
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨r, hr, huniq⟩ := CompactKappaCoreRadius.exists_unique_sup_ball_inv_sq
    hclosure D.scalarCurvature D.continuous_scalarCurvature hscalar p
  refine ⟨r, ⟨hr.1, (hsup r).trans hr.2⟩, ?_⟩
  intro s hs
  exact huniq s ⟨hs.1, (hsup s).symm.trans hs.2⟩

end PoincareConjecture
