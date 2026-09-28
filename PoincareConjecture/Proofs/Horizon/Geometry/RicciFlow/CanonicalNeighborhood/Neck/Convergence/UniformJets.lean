import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ChangingCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.TensorNorm
import PoincareConjecture.Proofs.Horizon.Topology.UniformConvergence.MovingPoints







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem PointedGeometricConvergence.tendstoUniformlyOn_cylinder_jet_error
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) {u : ℝ} (hu : u < 1)
    (hround : roundCylinderPullback (G.limitFlow.metricAt t) Φ =
      EvolvingRoundCylinderMetric u)
    (order : ℕ) {J : Set ℝ} (hJ : IsCompact J) :
    TendstoUniformlyOn
      (fun k => roundCylinderJetErrorSquared u
        (roundCylinderPullback ((S.flow (G.subsequence k)).metricAt t)
          (fun z => ((G.embedding k).toFun (0, Φ z)).2)) order)
      (fun _ => 0) atTop (Set.univ ×ˢ J) := by
  apply Poincare.Topology.tendstoUniformlyOn_prod_of_isCompact_of_locally_moving_points
    (g := fun _ : ℝ => (0 : ℝ))
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
  intro p _
  refine ⟨Metric.ball p (1 / 2), Metric.isOpen_ball, Metric.mem_ball_self (by norm_num), ?_⟩
  intro q hq
  have hpq (i : ℕ) : ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using (hq i).2
  have hc (v w : Fin 3) := G.smooth_zero_convergence_changing_cylinder_coefficients
    hzero hΦ p q hpq ht v w
  dsimp only at hc
  rw [hround] at hc
  have h := tendstoUniformlyOn_roundCylinder_changingChart_error_jetSum hu p q
    (Metric.isOpen_ball.prod isOpen_univ)
    (fun v w => (hc v w).1) (fun v w => (hc v w).2) order
    (isCompact_singleton.prod hJ)
    (show ({0} : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ J ⊆
        Metric.ball 0 (1 / 2) ×ˢ univ from by
      rintro ⟨x, z⟩ ⟨hx, hz⟩
      have hx0 : x = 0 := mem_singleton_iff.mp hx
      subst x
      exact ⟨Metric.mem_ball_self (by norm_num), mem_univ z⟩)
  have hh := (h.comp (fun z : ℝ => (0, z))).mono
    (show J ⊆ (fun z : ℝ => ((0 : EuclideanSpace ℝ (Fin 2)), z)) ⁻¹'
        (({0} : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ J) from
      fun z hz => ⟨mem_singleton 0, hz⟩)
  simpa only [roundCylinderJetErrorSquared, sphere_chart_center, Function.comp_def] using hh

end PoincareConjecture
