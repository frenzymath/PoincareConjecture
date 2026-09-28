import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Assembly

open Set Filter Metric Topology

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem

theorem exists_stageEmbedding_range_superset_of_closedBall
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (x : S.completedLimit.carrier) (R : ℝ) :
    ∃ n : ℕ,
      Metric.closedBall x R ⊆ Set.range (S.stageEmbedding n) := by
  obtain ⟨n, hn⟩ := hcover (dist S.completedLimit.base x + R)
  refine ⟨n, ?_⟩
  intro y hy
  apply hn
  rw [Metric.mem_closedBall] at hy ⊢
  calc
    dist y S.completedLimit.base ≤ dist y x + dist x S.completedLimit.base :=
      dist_triangle _ _ _
    _ ≤ R + dist x S.completedLimit.base := by gcongr
    _ = dist S.completedLimit.base x + R := by rw [dist_comm]; ring

theorem exists_eventually_stageEmbedding_range_superset_of_bounded
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    {K : Set S.completedLimit.carrier} (hK : Bornology.IsBounded K) :
    ∃ n : ℕ, K ⊆ Set.range (S.stageEmbedding n) ∧
      ∀ m : ℕ, n ≤ m → K ⊆ Set.range (S.stageEmbedding m) := by
  obtain ⟨R, hK⟩ :=
    (Metric.isBounded_iff_subset_closedBall S.completedLimit.base).mp hK
  obtain ⟨n, hn⟩ := hcover R
  refine ⟨n, hK.trans hn, ?_⟩
  intro m hnm
  exact (hK.trans hn).trans (S.range_stageEmbedding_mono hnm)

theorem cauchySeq_tendsto_mem_stage_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (u : ℕ → S.completedLimit.carrier) (hu : CauchySeq u)
    {y : S.completedLimit.carrier}
    (hy : Tendsto u atTop (𝓝 y)) :
    ∃ n : ℕ, y ∈ Set.range (S.stageEmbedding n) := by
  have hbounded : Bornology.IsBounded (Set.range u) := hu.isBounded_range
  obtain ⟨n, hn, _⟩ :=
    S.exists_eventually_stageEmbedding_range_superset_of_bounded hcover hbounded
  refine ⟨n, ?_⟩
  apply (S.isCompact_range_stageEmbedding n).isClosed.mem_of_tendsto hy
  exact Filter.Eventually.of_forall (fun k => hn (Set.mem_range.2 ⟨k, rfl⟩))

theorem exists_stageEmbedding_range_and_limit_of_cauchySeq
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (u : ℕ → S.completedLimit.carrier) (hu : CauchySeq u)
    {y : S.completedLimit.carrier}
    (hy : Tendsto u atTop (𝓝 y)) :
    ∃ n : ℕ, Set.range u ⊆ Set.range (S.stageEmbedding n) ∧
      y ∈ Set.range (S.stageEmbedding n) := by
  have hbounded : Bornology.IsBounded (Set.range u) := hu.isBounded_range
  obtain ⟨n, hn, _⟩ :=
    S.exists_eventually_stageEmbedding_range_superset_of_bounded hcover hbounded
  refine ⟨n, hn, ?_⟩
  apply (S.isCompact_range_stageEmbedding n).isClosed.mem_of_tendsto hy
  exact Filter.Eventually.of_forall (fun k => hn (Set.mem_range.2 ⟨k, rfl⟩))

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff
