import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.MetricBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.CenterBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.LocalOscillation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem reducedLengthPullback_pos (G : AncientCompactTimeConvergence S)
    (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) (x : G.limit.carrier.carrier) {τ : ℝ} (hτ : 0 < τ) :
    0 < G.reducedLengthPullback k x τ :=
  P.reducedLength_pos _ _ _ (mul_pos (S.scale_pos _) hτ)

theorem reducedLengthPullback_sqrt_local_oscillation
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {τ : ℝ} (hτ : 0 < τ) (q : G.limit.carrier.carrier) :
    ∃ U : Set G.limit.carrier.carrier, IsOpen U ∧ q ∈ U ∧
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ y ∈ U, ∀ z ∈ U,
        |Real.sqrt (G.reducedLengthPullback k y τ) -
          Real.sqrt (G.reducedLengthPullback k z τ)| ≤ C := by
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let a := (chartAt (EuclideanSpace ℝ (Fin n)) q) q
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_source a
    (mem_chart_target (EuclideanSpace ℝ (Fin n)) q)
  have hclosed : Metric.closedBall a (r / 2) ⊆ c.source := fun x hx =>
    hball (by
      change dist x a < r
      have hd : dist x a ≤ r / 2 := hx
      linarith)
  obtain ⟨B, hB⟩ := G.exists_eventually_sourceCoordinateChart_tangentNorm_bound P q
    (isCompact_closedBall a (r / 2)) hclosed hτ (le_refl τ)
  refine ⟨c '' Metric.ball a (r / 2),
    c.isOpen_image_of_subset_source Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans hclosed), ?_,
    (Real.sqrt (3 / τ) / 2 * B) * r, ?_⟩
  · refine ⟨a, Metric.mem_ball_self (by linarith), ?_⟩
    exact (chartAt (EuclideanSpace ℝ (Fin n)) q).left_inv (mem_chart_source _ q)
  · filter_upwards [hB, eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)]
      with k hk hk₀ y hy z hz
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth k q
    have h := P.rescaled_sqrt_reducedLength_coordinates_abs_le S.reference
      (S.rescaling (G.subsequence k)) hτ (G.sourceCoordinateChart k q) he hei hk.1
      (hk.2 τ ⟨le_rfl, le_rfl⟩) hx hw
    have hd : dist x w ≤ r := by
      have hd' := dist_triangle x a w
      rw [dist_comm a w] at hd'
      have hx' : dist x a < r / 2 := hx
      have hw' : dist w a < r / 2 := hw
      linarith
    change |Real.sqrt (reducedLength K.flow 0 S.reference (G.sourcePoint k (c x))
        (S.scale (G.subsequence k) * τ)) -
      Real.sqrt (reducedLength K.flow 0 S.reference (G.sourcePoint k (c w))
        (S.scale (G.subsequence k) * τ))| ≤ _
    rw [G.sourceCoordinateChart_apply k q hk₀ x,
      G.sourceCoordinateChart_apply k q hk₀ w] at h
    exact h.trans (mul_le_mul_of_nonneg_left hd (by positivity))

theorem reducedLengthPullback_eventually_bounded_on_compact
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {τ : ℝ} (hτ : 0 < τ) {A : Set G.limit.carrier.carrier} (hA : IsCompact A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ A, G.reducedLengthPullback k x τ ≤ C := by
  let : PreconnectedSpace G.limit.carrier.carrier := ⟨G.limit.carrier.connected.isPreconnected⟩
  have hbase : ∃ C : ℝ, ∀ᶠ k in atTop,
      |Real.sqrt (G.reducedLengthPullback k G.limit.base τ)| ≤ C := by
    refine ⟨Real.sqrt ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹), .of_forall ?_⟩
    intro k
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    unfold reducedLengthPullback
    rw [G.sourcePoint_base]
    exact S.reducedLength_at_base_time_le P _ hτ
  obtain ⟨C, hC, hc⟩ := Poincare.Analysis.eventually_uniform_abs_bound_on_compact_of_local_oscillation
    (fun k x => Real.sqrt (G.reducedLengthPullback k x τ))
    (G.reducedLengthPullback_sqrt_local_oscillation P hτ) hbase hA
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  filter_upwards [hc] with k hk x hx
  have hs := hk x hx
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hs
  nlinarith [Real.sq_sqrt (G.reducedLengthPullback_pos P k x hτ).le,
    Real.sqrt_nonneg (G.reducedLengthPullback k x τ)]

end PoincareConjecture.AncientCompactTimeConvergence
