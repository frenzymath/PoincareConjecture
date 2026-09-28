





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.RadialCoverage









open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem



theorem exists_stageEmbedding_eq_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (y : S.completedLimit.carrier) :
    ∃ n : ℕ, ∃ z : (S.stage n).carrier,
      S.stageEmbedding n z = y := by
  have hy : y ∈ ⋃ n : ℕ, Set.range (S.stageEmbedding n) := by
    rw [S.iUnion_range_stageEmbedding_eq_univ_of_radial_stage_coverage hcover]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
  rcases Set.mem_range.mp hyn with ⟨z, hzy⟩
  exact ⟨n, z, hzy⟩



theorem exists_stageEmbedding_range_superset_of_compact
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (K : Set S.completedLimit.carrier) (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ Set.range (S.stageEmbedding n) := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall S.completedLimit.base
  obtain ⟨n, hn⟩ := hcover R
  exact ⟨n, hKR.trans hn⟩



theorem isCompact_completedLimit_closedBall_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (x : S.completedLimit.carrier) (R : ℝ) :
    IsCompact (Metric.closedBall x R) := by
  letI : ProperSpace S.completedLimit.carrier :=
    S.properSpace_completedLimit_of_radial_stage_coverage hcover
  exact ProperSpace.isCompact_closedBall x R

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

end

