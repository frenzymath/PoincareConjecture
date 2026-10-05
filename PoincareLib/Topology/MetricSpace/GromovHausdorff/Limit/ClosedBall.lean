/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Bridges/ClosedBallStageBridge.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Limit.StageMetric

/-!
# closed-ball stage identifications

When a compact stage covers a closed ball in the completed common ambient, the
stage embedding restricts to a concrete isometry onto that ball.  This bridge
keeps the coverage premise explicit and exposes both the subtype equivalence
and its set-level image statement for finite-radius transport.
-/

open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

/-- **Math.** A based delta-net transports across a surjective isometry. -/
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

/-- **Math.** The restriction of a stage embedding to the corresponding
closed balls. -/
def stageClosedBallMap
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ) :
    Metric.closedBall (S.stage k).base R →
      Metric.closedBall S.completedLimit.base R :=
  fun x =>
    ⟨S.stageEmbedding k x,
      (S.mem_closedBall_stageEmbedding_iff k x R).2 x.property⟩

/-- **Math.** The restricted stage embedding preserves the subtype distances. -/
theorem stageClosedBallMap_isometry
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ) (R : ℝ) :
    Isometry (S.stageClosedBallMap k R) := by
  intro x y
  change edist (S.stageEmbedding k x) (S.stageEmbedding k y) = edist x y
  exact (S.stageEmbedding_isometry k).edist_eq _ _

/-- **Math.** A covered ambient closed ball is reached by the restricted stage
embedding. -/
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

/-- **Math.** The covered ambient closed ball and its stage closed-ball model are
isometric, with the stage embedding as the forward map. -/
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

/-- **Math.** The closed-ball equivalence preserves the distinguished basepoint. -/
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

/-- **Math.** The stage image of a covered closed ball is exactly the ambient
closed ball. -/
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

#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.stageClosedBallMap_isometry
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.stageClosedBallMap_surjective_of_coverage
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.stageClosedBallEquiv_of_coverage_base
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.image_stageEmbedding_closedBall_eq_of_coverage
