import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.NormalizedUniformJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.PointedGeometricConvergence
attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem tendstoUniformlyOn_normalized_cylinder_coefficient_error_jets
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b) {s : ℕ → ℝ} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hs : Tendsto s atTop (𝓝 s₀))
    (hround : (fun z v w => s₀ * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
      EvolvingRoundCylinderMetric 0)
    (v w : Fin 3) (m : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) :
    let B : ℕ → RoundCylinderTwoTensor := fun i z v w =>
      s i * roundCylinderPullback ((S.flow (G.subsequence i)).metricAt t)
        (fun z => ((G.embedding i).toFun (0, Φ z)).2) z v w
    TendstoUniformlyOn
      (fun i z => iteratedFDeriv ℝ m
        (fun x => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) x v w -
          roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) x v w) z.2)
      (fun _ => 0) atTop ((univ : Set UnitTwoSphere) ×ˢ K) := by
  dsimp only
  apply Poincare.Topology.tendstoUniformlyOn_prod_of_isCompact_of_locally_moving_points
    (g := fun _ : RoundCylinderCoordinates => (0 : ContinuousMultilinearMap ℝ
      (fun _ : Fin m => RoundCylinderCoordinates) ℝ))
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
  intro p _
  refine ⟨Metric.ball p (1 / 2), Metric.isOpen_ball, Metric.mem_ball_self (by norm_num), ?_⟩
  intro q hq
  have hpq (i : ℕ) : ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using (hq i).2
  exact (G.smooth_zero_convergence_normalized_changing_cylinder_coefficients
    hzero hΦ p q hpq ht hs₀ hs hround v w).2 m K hK hKU

theorem tendstoUniformlyOn_cylinder_parametrized_error_jets
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (m : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) :
    let f := fun q : UnitTwoSphere => fun x : RoundCylinderCoordinates =>
      Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1, x.2)
    TendstoUniformlyOn
      (fun i z => iteratedFDeriv ℝ m
        (fun x => ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
          (fun y => ((G.embedding i).toFun (0, f z.1 y)).2) x -
          (G.limitFlow.metricAt t).parametrizedCoefficients (f z.1) x) z.2)
      (fun _ => 0) atTop ((univ : Set UnitTwoSphere) ×ˢ K) := by
  dsimp only
  apply Poincare.Topology.tendstoUniformlyOn_prod_of_isCompact_of_locally_moving_points
    (Z := ContinuousMultilinearMap ℝ (fun _ : Fin m => RoundCylinderCoordinates)
      (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ))
    (g := fun _ : RoundCylinderCoordinates => 0)
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
  intro p _
  refine ⟨Metric.ball p (1 / 2), Metric.isOpen_ball, Metric.mem_ball_self (by norm_num), ?_⟩
  intro q hq
  have hpq (i : ℕ) : ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using (hq i).2
  exact (G.smooth_zero_convergence_changing_cylinder_parametrizations
    hzero hΦ p q hpq ht).2 m K hK hKU

end PoincareConjecture.PointedGeometricConvergence
