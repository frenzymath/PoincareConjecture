import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.Charts






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

theorem exists_eventually_sourceCoordinateChart_tangentNorm_bound
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ B : ℝ≥0, ∀ᶠ k : ℕ in atTop,
      A ⊆ (G.sourceCoordinateChart k q).source ∧
      ∀ τ ∈ Icc α β, ∀ x ∈ A, ∀ v : EuclideanSpace ℝ (Fin n),
        ((S.rescaling (G.subsequence k)).flow.metric (-τ)).tangentNorm
          (G.sourceCoordinateChart k q x)
          (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart k q) x v) ≤ B * ‖v‖ := by
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hβ : 0 < β := hα.trans_le hαβ
  have hc : ∀ x ∈ A, ContMDiffAt (𝓡 n) (𝓡 n) ∞ c x := fun x hx =>
    contMDiffOn_chart_symm.contMDiffAt (c.open_source.mem_nhds (hchart hx))
  obtain ⟨B, hB, hb⟩ := G.limit.flow.smooth.exists_uniform_coordinate_tangentNorm_bound
    isOpen_Iio hA hc (isCompact_singleton (x := -β))
      (by simpa only [singleton_subset_iff, mem_Iio] using neg_neg_of_pos hβ)
  refine ⟨Real.toNNReal (2 * B), ?_⟩
  have hK : IsCompact (c '' A) := hA.image_of_continuousOn (c.continuousOn.mono hchart)
  filter_upwards [G.eventually_subset_sourceCoordinateChart q hA hchart,
    G.eventually_pullback_tangentNorm_bounds hK (neg_neg_of_pos hβ)
      (by norm_num : (1 : ℝ) < 2),
    eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_timeWindow_mem_nhds (neg_neg_of_pos hβ)] with k hk hmetric hk₀ hkβ
  refine ⟨hk, ?_⟩
  intro τ hτ x hx v
  have hfixed : ((S.rescaling (G.subsequence k)).flow.metric (-β)).tangentNorm
      (G.sourceCoordinateChart k q x)
      (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart k q) x v) ≤ 2 * B * ‖v‖ := by
    rw [G.sourceCoordinateChart_tangentNorm_eq k q hk₀ hkβ (hk hx)]
    exact (hmetric (c x) (mem_image_of_mem c hx) (mfderiv (𝓡 n) (𝓡 n) c x v)).1.trans
      (by
        simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
          (hb (-β) (mem_singleton _) x hx v) (by norm_num : (0 : ℝ) ≤ 2)))
  have hmono (y : M) (w : TangentSpace (𝓡 n) y) :
      ((S.rescaling (G.subsequence k)).flow.metric (-τ)).tangentNorm y w ≤
        ((S.rescaling (G.subsequence k)).flow.metric (-β)).tangentNorm y w := by
    apply Real.sqrt_le_sqrt
    rw [(S.rescaling _).metric_scale (-τ) (by linarith [hτ.1]),
      (S.rescaling _).metric_scale (-β) (by linarith)]
    exact mul_le_mul_of_nonneg_left
      (((Classical.choice P.structural).structural M K).metric_monotone
        (S.scale (G.subsequence k) * (-β)) (S.scale (G.subsequence k) * (-τ))
        (mul_le_mul_of_nonneg_left (neg_le_neg hτ.2) (S.scale_pos _).le)
        (mul_nonpos_of_nonneg_of_nonpos (S.scale_pos _).le (by linarith [hτ.1])) y w)
      (div_nonneg (by norm_num) (S.scale_pos _).le)
  rw [Real.coe_toNNReal _ (by positivity)]
  exact (hmono _ _).trans hfixed

end PoincareConjecture.AncientCompactTimeConvergence
