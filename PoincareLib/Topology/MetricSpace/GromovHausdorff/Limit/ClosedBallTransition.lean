/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Foundations/ClosedBallTransition.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Limit.ClosedBall
import PoincareLib.Topology.MetricSpace.GromovHausdorff.Limit.Transitions

/-!
# closed-ball transition coherence

The compatible compact-stage system has transition chains on the full stage
carriers, while the finite-radius convergence interface uses closed-ball
subtypes.  This file restricts those chains to closed balls and records the
surjectivity obtained when the initial stage covers the same ambient ball as
the completed limit.
All coverage hypotheses remain explicit; the restriction itself only uses the
isometry and basepoint laws of the compatible system.
-/

open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** A finite transition chain restricts to a map between the
corresponding closed-ball subtypes. -/
def transitionChainClosedBallMap
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real) :
    Metric.closedBall (S.stage n).base R ->
      Metric.closedBall (S.stage (n + k)).base R :=
  fun x =>
    ⟨S.transitionChain n k x,
      Metric.mem_closedBall.mpr (by
        calc
          dist (S.transitionChain n k x) (S.stage (n + k)).base =
              dist (S.transitionChain n k x)
                (S.transitionChain n k (S.stage n).base) := by
            rw [S.transitionChain_base n k]
          _ = dist (x : (S.stage n).carrier) (S.stage n).base :=
            (S.transitionChain_isometry n k).dist_eq _ _
          _ <= R := x.property)⟩

/-- **Math.** The closed-ball transition restriction is an isometry. -/
theorem transitionChainClosedBallMap_isometry
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real) :
    Isometry (S.transitionChainClosedBallMap n k R) := by
  intro x y
  change edist (S.transitionChain n k x) (S.transitionChain n k y) =
    edist x y
  exact (S.transitionChain_isometry n k).edist_eq _ _

/-- **Math.** The restricted transition chain commutes with the ambient stage
embeddings, hence with the closed-ball stage maps. -/
theorem stageClosedBallMap_comp_transitionChainClosedBallMap
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real) :
    S.stageClosedBallMap (n + k) R ∘
        S.transitionChainClosedBallMap n k R =
      S.stageClosedBallMap n R := by
  funext x
  apply Subtype.ext
  change S.stageEmbedding (n + k) (S.transitionChain n k x) =
    S.stageEmbedding n x
  exact congrFun (S.stageEmbedding_comp_transitionChain n k) x

/-- **Math.** If the initial stage covers an ambient closed ball, the
restricted transition chain is surjective onto the corresponding target
closed-ball subtype. -/
theorem transitionChainClosedBallMap_surjective_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real)
    (hcover_n : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding n)) :
    Function.Surjective (S.transitionChainClosedBallMap n k R) := by
  intro y
  obtain ⟨x, hx⟩ :=
      S.stageClosedBallMap_surjective_of_coverage n R hcover_n
      (S.stageClosedBallMap (n + k) R y)
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply (S.stageEmbedding_isometry (n + k)).injective
  have hxy :
      S.stageEmbedding n x = S.stageEmbedding (n + k) y :=
    congrArg Subtype.val hx
  calc
    S.stageEmbedding (n + k)
        (S.transitionChainClosedBallMap n k R x) =
        S.stageEmbedding n x := by
          change S.stageEmbedding (n + k) (S.transitionChain n k x) =
            S.stageEmbedding n x
          exact congrFun (S.stageEmbedding_comp_transitionChain n k) x
    _ = S.stageEmbedding (n + k) y := hxy

/-- **Math.** Radial closed-ball coverage produces a stable stage for every
prescribed radius: all finite transition chains out of that stage are
surjective on the corresponding closed-ball subtypes. -/
theorem exists_transitionChainClosedBallMap_surjective_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n)) :
    ∀ R : ℝ, ∃ n : ℕ, ∀ k : ℕ,
      Function.Surjective
        (S.transitionChainClosedBallMap n k R) := by
  intro R
  obtain ⟨n, hn⟩ := hcover R
  refine ⟨n, ?_⟩
  intro k
  exact S.transitionChainClosedBallMap_surjective_of_coverage n k R hn

/-- **Math.** In the radius-enlarged form used by the radial converse, radial
coverage supplies a uniformly stable starting stage at each radius. -/
theorem transitionChainClosedBallMap_stable_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n)) :
    ∀ R : ℝ, ∃ n : ℕ, ∀ k : ℕ,
      Function.Surjective
        (S.transitionChainClosedBallMap n k (R + 1)) := by
  intro R
  obtain ⟨n, hn⟩ := hcover (R + 1)
  refine ⟨n, ?_⟩
  intro k
  exact S.transitionChainClosedBallMap_surjective_of_coverage n k (R + 1) hn

/-- **Math.** Coverage of the initial stage yields an isometric equivalence
between the two endpoint closed-ball subtypes. -/
noncomputable def transitionChainClosedBallEquiv_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real)
    (hcover_n : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding n)) :
    Metric.closedBall (S.stage n).base R ≃ᵢ
      Metric.closedBall (S.stage (n + k)).base R :=
  IsometryEquiv.mk'
    (S.transitionChainClosedBallMap n k R)
    (Function.surjInv
      (S.transitionChainClosedBallMap_surjective_of_coverage n k R
        hcover_n))
    (Function.surjInv_eq
      (S.transitionChainClosedBallMap_surjective_of_coverage n k R
        hcover_n))
    (S.transitionChainClosedBallMap_isometry n k R)

/-- **Math.** The closed-ball transition equivalence preserves the distinguished
basepoint whenever the radius is nonnegative. -/
theorem transitionChainClosedBallEquiv_of_coverage_base
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real)
    (hR : 0 <= R)
    (hcover_n : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding n)) :
    S.transitionChainClosedBallEquiv_of_coverage n k R hcover_n
        (⟨(S.stage n).base, Metric.mem_closedBall_self hR⟩) =
      (⟨(S.stage (n + k)).base, Metric.mem_closedBall_self hR⟩) := by
  apply Subtype.ext
  change S.transitionChain n k (S.stage n).base = (S.stage (n + k)).base
  exact S.transitionChain_base n k

/-- **Math.** The closed-ball transition equivalence is exactly the comparison
between the two endpoint stage maps into the common ambient ball. -/
theorem stageClosedBallEquiv_of_coverage_comp_transitionChainClosedBallEquiv
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real)
    (hcover_n : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding n))
    (hcover_m : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding (n + k))) :
    S.stageClosedBallEquiv_of_coverage (n + k) R hcover_m ∘
        S.transitionChainClosedBallEquiv_of_coverage n k R hcover_n =
      S.stageClosedBallEquiv_of_coverage n R hcover_n := by
  funext x
  apply Subtype.ext
  change S.stageEmbedding (n + k) (S.transitionChain n k x) =
    S.stageEmbedding n x
  exact congrFun (S.stageEmbedding_comp_transitionChain n k) x

/-! A stable closed-ball transition system forces the dense completed ambient
to be exhausted by one stage at each prescribed radius. -/

/-- **Math.** If one stage has surjective closed-ball transition chains at the
slightly enlarged radius `R + 1`, then the completed-limit closed ball of
radius `R` is contained in that stage's image. -/
theorem radial_stage_coverage_of_transitionChainClosedBallMap_surjective
    (S : CompatiblePointedCompactSystem.{u})
    (hstable : ∀ R : ℝ, ∃ n : ℕ, ∀ k : ℕ,
      Function.Surjective
        (S.transitionChainClosedBallMap n k (R + 1))) :
    ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) := by
  intro R
  obtain ⟨n, hn⟩ := hstable R
  refine ⟨n, ?_⟩
  let U : Set S.completedLimit.carrier :=
    ⋃ m : ℕ, Set.range (S.stageEmbedding m)
  have hU : Dense U := by
    simpa [U] using S.dense_iUnion_range_stageEmbedding
  have hC : IsClosed (Set.range (S.stageEmbedding n)) :=
    (S.isCompact_range_stageEmbedding n).isClosed
  intro y hy
  have hlocal : Metric.ball y 1 ∩ U ⊆
      Set.range (S.stageEmbedding n) := by
    rintro z ⟨hz, hzU⟩
    rcases Set.mem_iUnion.mp hzU with ⟨m, hzm⟩
    rcases Set.mem_range.mp hzm with ⟨x, rfl⟩
    have hzy : dist (S.stageEmbedding m x) y < 1 :=
      Metric.mem_ball.mp hz
    have hyR : dist y S.completedLimit.base ≤ R :=
      Metric.mem_closedBall.mp hy
    have hxball : x ∈
        Metric.closedBall (S.stage m).base (R + 1) := by
      apply Metric.mem_closedBall.mpr
      calc
        dist x (S.stage m).base =
            dist (S.stageEmbedding m x) S.completedLimit.base :=
          (S.dist_stageEmbedding_base m x).symm
        _ ≤ dist (S.stageEmbedding m x) y +
              dist y S.completedLimit.base := dist_triangle _ _ _
        _ ≤ 1 + R := add_le_add hzy.le hyR
        _ = R + 1 := by ring
    by_cases hmn : m ≤ n
    · exact (S.range_stageEmbedding_mono hmn) ⟨x, rfl⟩
    · have hnm : n ≤ m := Nat.le_of_lt (lt_of_not_ge hmn)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
      subst m
      obtain ⟨w, hw⟩ := hn k ⟨x, hxball⟩
      refine ⟨w, ?_⟩
      calc
        S.stageEmbedding n w =
            S.stageEmbedding (n + k) (S.transitionChain n k w) := by
          exact (congrFun (S.stageEmbedding_comp_transitionChain n k) w).symm
        _ = S.stageEmbedding (n + k) x := by
          apply congrArg (S.stageEmbedding (n + k))
          exact congrArg Subtype.val hw
  have hyball : y ∈ Metric.ball y 1 :=
    Metric.mem_ball_self (by norm_num)
  exact (closure_minimal hlocal hC)
    ((hU.open_subset_closure_inter Metric.isOpen_ball) hyball)

/-- **Math.** If each consecutive transition covers the strict inner ball of
its natural radius, every transition chain starting beyond a fixed radius is
surjective on that closed ball.  The strict radius buffer is preserved while
pulling a point back through successive transitions. -/
theorem transitionChainClosedBallMap_surjective_of_inner_ball_range
    (S : CompatiblePointedCompactSystem.{u})
    (hinner : ∀ i : ℕ,
      Metric.ball (S.stage (i + 1)).base (i : ℝ) ⊆
        Set.range (S.transition i))
    {n : ℕ} {R : ℝ} (hRn : R < (n : ℝ)) (k : ℕ) :
    Function.Surjective (S.transitionChainClosedBallMap n k R) := by
  induction k with
  | zero =>
      intro y
      exact ⟨y, rfl⟩
  | succ k ih =>
      intro y
      have hRnk : R < ((n + k : ℕ) : ℝ) :=
        hRn.trans_le (by exact_mod_cast Nat.le_add_right n k)
      have hyinner : (y : (S.stage (n + (k + 1))).carrier) ∈
          Metric.ball (S.stage (n + k + 1)).base ((n + k : ℕ) : ℝ) :=
        Metric.mem_ball.mpr (y.property.trans_lt hRnk)
      obtain ⟨x, hx⟩ := hinner (n + k) hyinner
      have hxball : x ∈ Metric.closedBall (S.stage (n + k)).base R := by
        apply Metric.mem_closedBall.mpr
        calc
          dist x (S.stage (n + k)).base =
              dist (S.transition (n + k) x)
                (S.transition (n + k) (S.stage (n + k)).base) :=
            ((S.transition_isometry (n + k)).dist_eq _ _).symm
          _ = dist (y : (S.stage (n + (k + 1))).carrier)
                (S.stage (n + k + 1)).base := by
            rw [hx, S.transition_base]
          _ ≤ R := y.property
      obtain ⟨w, hw⟩ := ih ⟨x, hxball⟩
      refine ⟨w, Subtype.ext ?_⟩
      change S.transition (n + k) (S.transitionChain n k w) = y
      exact (congrArg (S.transition (n + k)) (congrArg Subtype.val hw)).trans hx

/-- **Math.** Strict inner-ball coverage by consecutive compact transitions
implies radial closed-ball coverage of the completed inductive limit.  A stage
beyond `R + 1` captures the dense union locally, and its compact image is closed.
No length-space or boundary-surjectivity hypothesis is needed for this step. -/
theorem radial_stage_coverage_of_inner_ball_range
    (S : CompatiblePointedCompactSystem.{u})
    (hinner : ∀ i : ℕ,
      Metric.ball (S.stage (i + 1)).base (i : ℝ) ⊆
        Set.range (S.transition i)) :
    ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) := by
  apply S.radial_stage_coverage_of_transitionChainClosedBallMap_surjective
  intro R
  obtain ⟨n, hn⟩ := exists_nat_gt (R + 1)
  exact ⟨n, S.transitionChainClosedBallMap_surjective_of_inner_ball_range hinner hn⟩

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

end

#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.transitionChainClosedBallMap_isometry
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.stageClosedBallMap_comp_transitionChainClosedBallMap
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.transitionChainClosedBallMap_surjective_of_coverage
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.exists_transitionChainClosedBallMap_surjective_of_radial_stage_coverage
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.transitionChainClosedBallMap_stable_of_radial_stage_coverage
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.transitionChainClosedBallEquiv_of_coverage_base
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.stageClosedBallEquiv_of_coverage_comp_transitionChainClosedBallEquiv
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.radial_stage_coverage_of_transitionChainClosedBallMap_surjective
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.transitionChainClosedBallMap_surjective_of_inner_ball_range
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.radial_stage_coverage_of_inner_ball_range
