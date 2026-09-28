import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.CompactStage

open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem

theorem dist_stageEmbedding_base
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ)
    (x : (S.stage n).carrier) :
    dist (S.stageEmbedding n x) S.completedLimit.base =
      dist x (S.stage n).base := by
  rw [← S.stageEmbedding_base n]
  exact (S.stageEmbedding_isometry n).dist_eq _ _

theorem mem_closedBall_stageEmbedding_iff
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ)
    (x : (S.stage n).carrier) (R : ℝ) :
    S.stageEmbedding n x ∈ Metric.closedBall S.completedLimit.base R ↔
      x ∈ Metric.closedBall (S.stage n).base R := by
  rw [Metric.mem_closedBall, Metric.mem_closedBall,
    ← S.stageEmbedding_base n, (S.stageEmbedding_isometry n).dist_eq]

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

end
