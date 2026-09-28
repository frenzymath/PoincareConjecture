import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.StageMetric

open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

theorem IsDeltaNet.image_isometryEquiv
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) {δ : ℝ} {x : X} {L : Set X}
    (hL : IsDeltaNet δ x L) :
    IsDeltaNet δ (e x) (e '' L) := by
  rcases hL with ⟨hx, hcover, ε, hε, hsep⟩
  refine ⟨⟨x, hx, rfl⟩, ?_, ε, hε, ?_⟩
  · intro y
    obtain ⟨z, hz, hzy⟩ := hcover (e.symm y)
    refine ⟨e z, ⟨z, hz, rfl⟩, ?_⟩
    calc
      dist y (e z) = dist (e (e.symm y)) (e z) := by
        rw [e.apply_symm_apply]
      _ = dist (e.symm y) z := e.isometry.dist_eq _ _
      _ < δ := hzy
  · intro u v hu hv huv
    rcases hu with ⟨u', hu', rfl⟩
    rcases hv with ⟨v', hv', rfl⟩
    have huv' : u' ≠ v' := by
      intro huv'
      apply huv
      rw [huv']
    calc
      ε ≤ dist u' v' := hsep hu' hv' huv'
      _ = dist (e u') (e v') := (e.isometry.dist_eq _ _).symm

namespace CompatiblePointedCompactSystem

def stageClosedBallMap
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ) :
    Metric.closedBall (S.stage k).base R →
      Metric.closedBall S.completedLimit.base R :=
  fun x =>
    ⟨S.stageEmbedding k x,
      (S.mem_closedBall_stageEmbedding_iff k x R).2 x.property⟩

theorem stageClosedBallMap_isometry
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ) :
    Isometry (S.stageClosedBallMap k R) := by
  intro x y
  change edist (S.stageEmbedding k x) (S.stageEmbedding k y) = edist x y
  exact (S.stageEmbedding_isometry k).edist_eq _ _

theorem stageClosedBallMap_surjective_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ)
    (hcover : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding k)) :
    Function.Surjective (S.stageClosedBallMap k R) := by
  intro y
  obtain ⟨x, hx⟩ := hcover y.property
  have hx' : S.stageEmbedding k x ∈
      Metric.closedBall S.completedLimit.base R := by
    rw [hx]
    exact y.property
  have hxball : x ∈ Metric.closedBall (S.stage k).base R :=
    (S.mem_closedBall_stageEmbedding_iff k x R).mp hx'
  refine ⟨⟨x, hxball⟩, ?_⟩
  apply Subtype.ext
  exact hx

noncomputable def stageClosedBallEquiv_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ)
    (hcover : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding k)) :
    Metric.closedBall (S.stage k).base R ≃ᵢ
      Metric.closedBall S.completedLimit.base R :=
  IsometryEquiv.mk' (S.stageClosedBallMap k R)
    (Function.surjInv (S.stageClosedBallMap_surjective_of_coverage k R hcover))
    (Function.surjInv_eq
      (S.stageClosedBallMap_surjective_of_coverage k R hcover))
    (S.stageClosedBallMap_isometry k R)

theorem stageClosedBallEquiv_of_coverage_base
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ)
    (hR : 0 ≤ R)
    (hcover : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding k)) :
    S.stageClosedBallEquiv_of_coverage k R hcover
        (⟨(S.stage k).base, Metric.mem_closedBall_self hR⟩) =
      (⟨S.completedLimit.base, Metric.mem_closedBall_self hR⟩) := by
  apply Subtype.ext
  change S.stageEmbedding k (S.stage k).base = S.completedLimit.base
  exact S.stageEmbedding_base k

theorem image_stageEmbedding_closedBall_eq_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ)
    (hcover : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding k)) :
    S.stageEmbedding k '' Metric.closedBall (S.stage k).base R =
      Metric.closedBall S.completedLimit.base R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (S.mem_closedBall_stageEmbedding_iff k x R).2 hx
  · intro hy
    obtain ⟨x, hx⟩ := hcover hy
    have hx' : S.stageEmbedding k x ∈
        Metric.closedBall S.completedLimit.base R := by
      rw [hx]
      exact hy
    have hxball : x ∈ Metric.closedBall (S.stage k).base R :=
      (S.mem_closedBall_stageEmbedding_iff k x R).mp hx'
    exact ⟨x, hxball, hx⟩

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

end
