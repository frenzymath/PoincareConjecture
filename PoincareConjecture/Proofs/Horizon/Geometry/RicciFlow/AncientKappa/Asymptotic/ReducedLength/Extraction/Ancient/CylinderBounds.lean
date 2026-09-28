import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.CompactBounds


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

theorem reducedLengthPullback_eventually_bounded_on_compact_cylinder
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    {A : Set G.limit.carrier.carrier} (hA : IsCompact A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ A, ∀ τ ∈ Icc α β,
      G.reducedLengthPullback k x τ ≤ C := by
  obtain ⟨C, hC, hc⟩ := G.reducedLengthPullback_eventually_bounded_on_compact P
    (hα.trans_le hαβ) hA
  refine ⟨C * β ^ 2 / α ^ 2, by positivity, ?_⟩
  filter_upwards [hc] with k hk x hx τ hτ
  exact P.rescaled_reducedLength_le_later_bound S.reference (G.sourcePoint k x)
    (S.scale_pos _) hα hτ (hk x hx)

theorem reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : G.limit.carrier.carrier)
    {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∃ D : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      LipschitzOnWith D
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
          G.reducedLengthPullback k ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1) z.2)
        (Metric.closedBall a r ×ˢ Icc α β) ∧
      ∀ z ∈ Metric.closedBall a r ×ˢ Icc α β,
        G.reducedLengthPullback k ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1) z.2 ∈ Icc 0 C := by
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hcompact : IsCompact (c '' Metric.closedBall a (2 * r)) :=
    (isCompact_closedBall a (2 * r)).image_of_continuousOn (c.continuousOn.mono hchart)
  obtain ⟨A, hA, ha⟩ := G.reducedLengthPullback_eventually_bounded_on_compact P
    (hα.trans_le hαβ) hcompact
  obtain ⟨B, hb⟩ := G.exists_eventually_sourceCoordinateChart_tangentNorm_bound P q
    (isCompact_closedBall a (2 * r)) hchart hα hαβ
  refine ⟨Real.toNNReal
    (2 * Real.sqrt (A * β ^ 2 / α ^ 2) * (Real.sqrt (3 / α) / 2 * B) +
      2 * A * β ^ 2 / α ^ 3), A * β ^ 2 / α ^ 2, by positivity, ?_⟩
  filter_upwards [ha, hb, eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)]
    with k hk hbk hk₀
  obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth k q
  have hpoint : ∀ x ∈ Metric.ball a (2 * r),
      reducedLength K.flow 0 S.reference (G.sourceCoordinateChart k q x)
        (S.scale (G.subsequence k) * β) ≤ A := by
    intro x hx
    rw [G.sourceCoordinateChart_apply k q hk₀]
    exact hk (c x) (mem_image_of_mem c (Metric.ball_subset_closedBall hx))
  have hlip := P.rescaled_reducedLength_coordinates_lipschitzOn_cylinder S.reference
    (S.rescaling (G.subsequence k)) hα (G.sourceCoordinateChart k q) he hei hA hbk.1 hbk.2 hpoint
  have hsub : Metric.closedBall a r ⊆ Metric.ball a (2 * r) := by
    intro x hx
    change dist x a < 2 * r
    have hd : dist x a ≤ r := hx
    linarith
  have hfun : (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      reducedLength K.flow 0 S.reference (G.sourceCoordinateChart k q z.1)
        (S.scale (G.subsequence k) * z.2)) =
    (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      G.reducedLengthPullback k (c z.1) z.2) := by
    funext z
    rw [G.sourceCoordinateChart_apply k q hk₀]
    rfl
  rw [hfun] at hlip
  refine ⟨hlip.mono (Set.prod_mono hsub Subset.rfl), ?_⟩
  intro z hz
  refine ⟨(G.reducedLengthPullback_pos P k (c z.1) (hα.trans_le hz.2.1)).le, ?_⟩
  exact P.rescaled_reducedLength_le_later_bound S.reference (G.sourcePoint k (c z.1))
    (S.scale_pos _) hα hz.2 (hk (c z.1)
      (mem_image_of_mem c (Metric.ball_subset_closedBall (hsub hz.1))))

end PoincareConjecture.AncientCompactTimeConvergence
