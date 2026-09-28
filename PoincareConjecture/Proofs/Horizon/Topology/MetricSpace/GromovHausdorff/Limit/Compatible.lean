





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Packing.Compactness
import Mathlib.Topology.MetricSpace.Gluing














open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u




structure CompatiblePointedCompactSystem where
  stage : ℕ → PointedCompactMetricSpace.{u}
  transition : ∀ n, (stage n).carrier → (stage (n + 1)).carrier
  transition_isometry : ∀ n, Isometry (transition n)
  transition_base : ∀ n, transition n (stage n).base = (stage (n + 1)).base

namespace CompatiblePointedCompactSystem



def inductiveLimit
    (S : CompatiblePointedCompactSystem.{u}) : BasedMetricSpaceBundle.{u} :=
  { carrier := Metric.InductiveLimit S.transition_isometry
    metric := inferInstance
    base := Metric.toInductiveLimit S.transition_isometry 0 (S.stage 0).base }



def stageMap (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    (S.stage n).carrier → S.inductiveLimit.carrier :=
  Metric.toInductiveLimit S.transition_isometry n

theorem stageMap_isometry (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    Isometry (S.stageMap n) :=
  Metric.toInductiveLimit_isometry S.transition_isometry n


theorem stageMap_succ_comp_transition
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    S.stageMap (n + 1) ∘ S.transition n = S.stageMap n :=
  Metric.toInductiveLimit_commute S.transition_isometry n


theorem stageMap_base (S : CompatiblePointedCompactSystem.{u}) :
    ∀ n, S.stageMap n (S.stage n).base = S.inductiveLimit.base := by
  intro n
  induction n with
  | zero =>
      change Metric.toInductiveLimit S.transition_isometry 0 (S.stage 0).base =
        Metric.toInductiveLimit S.transition_isometry 0 (S.stage 0).base
      rfl
  | succ n ih =>
      have hcomm := congrFun (S.stageMap_succ_comp_transition n) (S.stage n).base
      rw [Function.comp_apply, S.transition_base n] at hcomm
      exact hcomm.trans ih



def completedLimit
    (S : CompatiblePointedCompactSystem.{u}) : BasedMetricSpaceBundle.{u} :=
  { carrier := UniformSpace.Completion S.inductiveLimit.carrier
    metric := inferInstance
    base := (S.inductiveLimit.base :
      UniformSpace.Completion S.inductiveLimit.carrier) }


def stageEmbedding (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    (S.stage n).carrier → S.completedLimit.carrier :=
  ((↑) : S.inductiveLimit.carrier →
      UniformSpace.Completion S.inductiveLimit.carrier) ∘ S.stageMap n

theorem stageEmbedding_isometry
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    Isometry (S.stageEmbedding n) :=
  UniformSpace.Completion.coe_isometry.comp (S.stageMap_isometry n)


theorem stageEmbedding_succ_comp_transition
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    S.stageEmbedding (n + 1) ∘ S.transition n = S.stageEmbedding n := by
  change ((↑) : S.inductiveLimit.carrier →
      UniformSpace.Completion S.inductiveLimit.carrier) ∘
      (S.stageMap (n + 1) ∘ S.transition n) =
    ((↑) : S.inductiveLimit.carrier →
      UniformSpace.Completion S.inductiveLimit.carrier) ∘ S.stageMap n
  rw [S.stageMap_succ_comp_transition n]


theorem stageEmbedding_base
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    S.stageEmbedding n (S.stage n).base = S.completedLimit.base := by
  change (S.stageMap n (S.stage n).base :
      UniformSpace.Completion S.inductiveLimit.carrier) =
    (S.inductiveLimit.base :
      UniformSpace.Completion S.inductiveLimit.carrier)
  rw [S.stageMap_base n]


theorem isCompact_range_stageEmbedding
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    IsCompact (Set.range (S.stageEmbedding n)) :=
  isCompact_range (S.stageEmbedding_isometry n).continuous




theorem dense_iUnion_range_stageEmbedding
    (S : CompatiblePointedCompactSystem.{u}) :
    Dense (⋃ n : ℕ, Set.range (S.stageEmbedding n)) := by
  let U : Set S.inductiveLimit.carrier :=
    ⋃ n : ℕ, Set.range (S.stageMap n)
  have hU : Dense U := by
    change Dense (⋃ n : ℕ,
      Set.range (Metric.toInductiveLimit S.transition_isometry n))
    exact Metric.dense_iUnion_range_toInductiveLimit S.transition_isometry
  have hcompletion :
      Dense (((↑) : S.inductiveLimit.carrier →
        UniformSpace.Completion S.inductiveLimit.carrier) '' U) :=
    (UniformSpace.Completion.isDenseInducing_coe.dense_image).mpr hU
  have hsets :
      (((↑) : S.inductiveLimit.carrier →
        UniformSpace.Completion S.inductiveLimit.carrier) '' U) =
        (⋃ n : ℕ, Set.range (S.stageEmbedding n)) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rcases mem_iUnion.1 hx with ⟨n, hxn⟩
      rcases mem_range.1 hxn with ⟨z, hzx⟩
      refine mem_iUnion.2 ⟨n, mem_range.2 ⟨z, ?_⟩⟩
      change (S.stageMap n z : UniformSpace.Completion S.inductiveLimit.carrier) = y
      calc
        (S.stageMap n z : UniformSpace.Completion S.inductiveLimit.carrier) =
            (x : UniformSpace.Completion S.inductiveLimit.carrier) :=
          congrArg (fun w : S.inductiveLimit.carrier =>
            (w : UniformSpace.Completion S.inductiveLimit.carrier)) hzx
        _ = y := hxy
    · intro hy
      rcases mem_iUnion.1 hy with ⟨n, hyn⟩
      rcases mem_range.1 hyn with ⟨z, hzy⟩
      refine ⟨S.stageMap n z,
        mem_iUnion.2 ⟨n, mem_range.2 ⟨z, rfl⟩⟩, ?_⟩
      exact hzy
  rw [hsets] at hcompletion
  exact hcompletion





def stageRealization (S : CompatiblePointedCompactSystem.{u}) (m n : ℕ) :
    PointedGHRealization
      (S.stage m).toFiniteDiameterBasedMetricSpace
      (S.stage n).toFiniteDiameterBasedMetricSpace :=
  { ambient := S.completedLimit
    left := S.stageEmbedding m
    right := S.stageEmbedding n
    left_isometry := S.stageEmbedding_isometry m
    right_isometry := S.stageEmbedding_isometry n
    left_base := S.stageEmbedding_base m
    right_base := S.stageEmbedding_base n }



theorem pointedGHDistance_stage_le_common_realization
    (S : CompatiblePointedCompactSystem.{u}) (m n : ℕ) :
    pointedGHDistance
        (S.stage m).toFiniteDiameterBasedMetricSpace
        (S.stage n).toFiniteDiameterBasedMetricSpace ≤
      pointedHausdorffDist (S.stageRealization m n) :=
  pointedGHDistance_le_realization (S.stageRealization m n)


theorem range_stageEmbedding_mono_succ
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    Set.range (S.stageEmbedding n) ⊆
      Set.range (S.stageEmbedding (n + 1)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨S.transition n x, ?_⟩
  have hcomm := congrFun (S.stageEmbedding_succ_comp_transition n) x
  simpa [Function.comp_apply] using hcomm




theorem properSpace_completedLimit_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n)) :
    ProperSpace S.completedLimit.carrier := by
  refine ⟨fun x R ↦ ?_⟩
  obtain ⟨n, hn⟩ := hcover (dist S.completedLimit.base x + R)
  apply (S.isCompact_range_stageEmbedding n).of_isClosed_subset
    Metric.isClosed_closedBall
  intro y hy
  apply hn
  rw [Metric.mem_closedBall] at hy ⊢
  calc
    dist y S.completedLimit.base ≤ dist y x + dist x S.completedLimit.base :=
      dist_triangle _ _ _
    _ ≤ R + dist x S.completedLimit.base := by gcongr
    _ = dist S.completedLimit.base x + R := by rw [dist_comm]; ring

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

