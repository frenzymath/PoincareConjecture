import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Surrounding

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

theorem RiemannianMetric.PointSoulData.center_not_mem_neck_sphere
    {g : RiemannianMetric 3 M} (S : RiemannianMetric.PointSoulData g)
    (hc : MetricComplete g) (N : EpsilonNeck g)
    (hN : N.epsilon ≤ neckSeparationThreshold) :
    S.center ∉ N.central_sphere := by
  obtain ⟨A, B, _, _, _, _, _, hcover, _, _, _, hcenter, _, _⟩ :=
    S.exists_surrounding_neck_regions hc N hN
  have hmem : S.center ∈ A ∪ B := Or.inl hcenter
  rwa [hcover] at hmem

theorem RiemannianMetric.PointSoulData.neck_center_ne
    {g : RiemannianMetric 3 M} (S : RiemannianMetric.PointSoulData g)
    (hc : MetricComplete g) (N : EpsilonNeck g)
    (hN : N.epsilon ≤ neckSeparationThreshold) :
    N.center ≠ S.center := by
  intro heq
  apply S.center_not_mem_neck_sphere hc N hN
  simpa only [heq] using N.center_on_central_sphere

theorem RiemannianMetric.PointSoulData.not_strongEvolvingNeck_center
    [T2Space M] [SecondCountableTopology M]
    (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
    {epsilon : ℝ} (hsmall : epsilon ≤ neckSeparationThreshold) :
    ¬ ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = S.center := by
  rintro ⟨N, hcenter⟩
  exact S.neck_center_ne (K.complete 0 le_rfl) N.terminal_neck
    (N.terminal_epsilon.trans_le hsmall) (N.terminal_center.trans hcenter)

end PoincareConjecture
