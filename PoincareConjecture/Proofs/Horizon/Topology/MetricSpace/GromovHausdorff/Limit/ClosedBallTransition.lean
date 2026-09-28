





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.ClosedBall
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Transitions












open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem



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


theorem transitionChainClosedBallMap_isometry
    (S : CompatiblePointedCompactSystem.{u}) (n k : Nat) (R : Real) :
    Isometry (S.transitionChainClosedBallMap n k R) := by
  intro x y
  change edist (S.transitionChain n k x) (S.transitionChain n k y) =
    edist x y
  exact (S.transitionChain_isometry n k).edist_eq _ _



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

