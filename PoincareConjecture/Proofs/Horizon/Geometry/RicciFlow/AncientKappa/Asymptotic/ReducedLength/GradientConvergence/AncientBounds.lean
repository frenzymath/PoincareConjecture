import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.CylinderBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology NNReal

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem reducedLengthPullback_coordinates_eq (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier)
    (hk : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ)) (τ : ℝ) :
    (fun x => reducedLength K.flow 0 S.reference (G.sourceCoordinateChart k q x)
      (S.scale (G.subsequence k) * τ)) =
    (fun x => G.reducedLengthPullback k
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) τ) := by
  funext x
  rw [G.sourceCoordinateChart_apply k q hk]
  rfl

theorem exists_eventually_reducedLengthPullback_weak_data_bounds
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∃ L : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      LipschitzOnWith L (fun x => G.reducedLengthPullback k
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) τ) (Metric.ball a r) ∧
      Metric.closedBall a r ⊆ (G.sourceCoordinateChart k q).source ∧
      (∀ x ∈ Metric.ball a r,
        |(S.rescaling (G.subsequence k)).reducedLengthCoordinateSource
          S.reference τ (G.sourceCoordinateChart k q) x| ≤ C) ∧
      (∀ i x, x ∈ Metric.ball a r →
        |(S.rescaling (G.subsequence k)).reducedLengthCoordinateFlux
          S.reference τ (G.sourceCoordinateChart k q) i x| ≤ C) := by
  have hsmall : Metric.closedBall a r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨L, B, hB, hLip⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hτ (le_refl τ) hchart
  obtain ⟨D, hD, hbounds⟩ := G.exists_eventually_sourceCoordinateChart_coefficient_bounds
    q (isCompact_closedBall a r) hsmall hτ
  let C := ((B + (n : ℝ) / 2) / τ) * D + (n : ℝ) * D * L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨L, C, hC, ?_⟩
  filter_upwards [hLip, hbounds, G.eventually_subset_sourceCoordinateChart
    q (isCompact_closedBall a r) hsmall,
    eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)]
    with k hkLip hkB hkSource hk₀
  have hlip : LipschitzOnWith L (fun x => G.reducedLengthPullback k
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) τ) (Metric.ball a r) := by
    simpa only [mul_one, Function.comp_def] using hkLip.1.comp
      (LipschitzWith.prodMk_right τ).lipschitzOnWith
      (fun x hx => ⟨Metric.ball_subset_closedBall hx, le_rfl, le_rfl⟩)
  have hfun := G.reducedLengthPullback_coordinates_eq k q hk₀ τ
  have hlip' : LipschitzOnWith L (fun x => reducedLength K.flow 0 S.reference
      (G.sourceCoordinateChart k q x) (S.scale (G.subsequence k) * τ)) (Metric.ball a r) :=
    hfun ▸ hlip
  refine ⟨hlip, hkSource, ?_, ?_⟩
  · intro x hx
    have hval := hkLip.2 (x, τ) ⟨Metric.ball_subset_closedBall hx, le_rfl, le_rfl⟩
    rw [← congrFun hfun x] at hval
    have h := (S.rescaling (G.subsequence k)).abs_reducedLengthCoordinateSource_le
      S.reference hτ (G.sourceCoordinateChart k q) hval.1 hval.2
      (hkB x (Metric.ball_subset_closedBall hx)).1
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · intro i x hx
    have h := (S.rescaling (G.subsequence k)).abs_reducedLengthCoordinateFlux_le
      S.reference τ (G.sourceCoordinateChart k q) Metric.isOpen_ball hlip' hD
      (fun y hy => (hkB y (Metric.ball_subset_closedBall hy)).2) hx i
    exact h.trans (le_add_of_nonneg_left (by positivity))

end PoincareConjecture.AncientCompactTimeConvergence
