import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology NNReal

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

namespace AncientRescaling

theorem scalar_le_rescaledReducedLength {s : ℝ} (R : AncientRescaling K s)
    (P : AncientAsymptoticSolitonPredecessors K) (p x : M) {τ : ℝ} (hτ : 0 < τ) :
    (R.flow.connection (-τ)).scalarCurvature x ≤
      3 * reducedLength K.flow 0 p x (s * τ) / τ := by
  have hscalar := R.scalar_scale (-τ) (neg_neg_of_pos hτ) x
  rw [show s * -τ = 0 - s * τ by ring] at hscalar
  rw [hscalar]
  have h := mul_le_mul_of_nonneg_left
    (P.scalar_le_reducedLength p x (s * τ) (mul_pos R.tau_pos hτ)) R.tau_pos.le
  convert! h using 1 <;> field_simp [R.tau_pos.ne', hτ.ne']

theorem scalar_nonneg_of_predecessors {s : ℝ} (R : AncientRescaling K s)
    (P : AncientAsymptoticSolitonPredecessors K) (x : M) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ (R.flow.connection (-τ)).scalarCurvature x := by
  rw [R.scalar_scale (-τ) (neg_neg_of_pos hτ)]
  exact mul_nonneg R.tau_pos.le
    (((Classical.choice P.structural).structural M K).scalar_pos (s * -τ)
      (mul_nonpos_of_nonneg_of_nonpos R.tau_pos.le (neg_nonpos.mpr hτ.le)) x).le

end AncientRescaling

namespace AncientCompactTimeConvergence

theorem tendsto_sourceCoordinateChart_scalarCurvature
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun k => ((S.rescaling (G.subsequence k)).flow.connection (-τ)).scalarCurvature
      (G.sourceCoordinateChart k q x)) atTop
      (𝓝 ((G.limit.flow.connection (-τ)).scalarCurvature
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x))) := by
  let y := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x
  apply (G.tendsto_scalarCurvature (-τ) (neg_neg_of_pos hτ) y).congr'
  filter_upwards [eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_timeWindow_mem_nhds (neg_neg_of_pos hτ), G.eventually_mem_exhaustion y]
    with k hk₀ hkt hky
  rw [G.sourceCoordinateChart_apply k q hk₀,
    G.sourcePoint_eq_at k (mem_of_mem_nhds hkt) hky]

theorem exists_eventually_sourceCoordinateChart_scalar_bound
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ Metric.closedBall a r,
      0 ≤ ((S.rescaling (G.subsequence k)).flow.connection (-τ)).scalarCurvature
        (G.sourceCoordinateChart k q x) ∧
      ((S.rescaling (G.subsequence k)).flow.connection (-τ)).scalarCurvature
        (G.sourceCoordinateChart k q x) ≤ C := by
  obtain ⟨L, C, hC, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hτ (le_refl τ) hchart
  refine ⟨3 * C / τ, by positivity, ?_⟩
  filter_upwards [hLip, eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)]
    with k hk hk₀ x hx
  refine ⟨(S.rescaling (G.subsequence k)).scalar_nonneg_of_predecessors P _ hτ, ?_⟩
  have hb := (hk.2 (x, τ) ⟨hx, ⟨le_rfl, le_rfl⟩⟩).2
  have hfun := G.reducedLengthPullback_coordinates_eq k q hk₀ τ
  rw [← congrFun hfun x] at hb
  exact ((S.rescaling (G.subsequence k)).scalar_le_rescaledReducedLength P S.reference _ hτ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hτ.le)

end AncientCompactTimeConvergence
end PoincareConjecture
