/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Bridges/CompatibleBallLimits.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Packing.Compactness
import Mathlib.Topology.MetricSpace.Gluing

/-!
# compatible compact-ball limits

Finite-radius Gromov--Hausdorff extraction produces one compact limit at each
radius.  This file isolates the additional compatibility data needed to glue
those compact limits.  From basepoint-preserving isometric transition maps it
constructs a single complete common ambient space containing every stage.

The final properness theorem states the remaining radial exhaustion premise
explicitly: every bounded ball in the completed limit must already lie in one
compact stage image.
-/

open Set Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

/-- **Math.** A sequence of pointed compact metric spaces with basepoint-preserving
isometric transition maps.  This is the compatibility datum missing from the
independent finite-radius GH classes produced by diagonal extraction. -/
structure CompatiblePointedCompactSystem where
  stage : ℕ → PointedCompactMetricSpace.{u}
  transition : ∀ n, (stage n).carrier → (stage (n + 1)).carrier
  transition_isometry : ∀ n, Isometry (transition n)
  transition_base : ∀ n, transition n (stage n).base = (stage (n + 1)).base

namespace CompatiblePointedCompactSystem

/-- **Math.** The metric inductive limit of a compatible system, based at the common
image of the stage basepoints. -/
def inductiveLimit
    (S : CompatiblePointedCompactSystem.{u}) : BasedMetricSpaceBundle.{u} :=
  { carrier := Metric.InductiveLimit S.transition_isometry
    metric := inferInstance
    base := Metric.toInductiveLimit S.transition_isometry 0 (S.stage 0).base }

/-- **Math.** The canonical isometric map from one compact stage to the inductive
limit. -/
def stageMap (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    (S.stage n).carrier → S.inductiveLimit.carrier :=
  Metric.toInductiveLimit S.transition_isometry n

theorem stageMap_isometry (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    Isometry (S.stageMap n) :=
  Metric.toInductiveLimit_isometry S.transition_isometry n

/-- **Math.** Consecutive stage maps agree after applying the transition map. -/
theorem stageMap_succ_comp_transition
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    S.stageMap (n + 1) ∘ S.transition n = S.stageMap n :=
  Metric.toInductiveLimit_commute S.transition_isometry n

/-- **Math.** Every stage basepoint has the same image in the inductive limit. -/
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

/-- **Math.** Complete the metric inductive limit.  Unlike the raw union, this carrier
has a `CompleteSpace` instance without any further hypothesis. -/
def completedLimit
    (S : CompatiblePointedCompactSystem.{u}) : BasedMetricSpaceBundle.{u} :=
  { carrier := UniformSpace.Completion S.inductiveLimit.carrier
    metric := inferInstance
    base := (S.inductiveLimit.base :
      UniformSpace.Completion S.inductiveLimit.carrier) }

/-- **Math.** The canonical stage embedding into the completed common ambient space. -/
def stageEmbedding (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    (S.stage n).carrier → S.completedLimit.carrier :=
  ((↑) : S.inductiveLimit.carrier →
      UniformSpace.Completion S.inductiveLimit.carrier) ∘ S.stageMap n

theorem stageEmbedding_isometry
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    Isometry (S.stageEmbedding n) :=
  UniformSpace.Completion.coe_isometry.comp (S.stageMap_isometry n)

/-- **Math.** The completed stage embeddings retain the transition compatibility. -/
theorem stageEmbedding_succ_comp_transition
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    S.stageEmbedding (n + 1) ∘ S.transition n = S.stageEmbedding n := by
  change ((↑) : S.inductiveLimit.carrier →
      UniformSpace.Completion S.inductiveLimit.carrier) ∘
      (S.stageMap (n + 1) ∘ S.transition n) =
    ((↑) : S.inductiveLimit.carrier →
      UniformSpace.Completion S.inductiveLimit.carrier) ∘ S.stageMap n
  rw [S.stageMap_succ_comp_transition n]

/-- **Math.** Every compact-stage basepoint maps to the completed-limit basepoint. -/
theorem stageEmbedding_base
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    S.stageEmbedding n (S.stage n).base = S.completedLimit.base := by
  change (S.stageMap n (S.stage n).base :
      UniformSpace.Completion S.inductiveLimit.carrier) =
    (S.inductiveLimit.base :
      UniformSpace.Completion S.inductiveLimit.carrier)
  rw [S.stageMap_base n]

/-- **Math.** Each stage has compact image in the completed common ambient space. -/
theorem isCompact_range_stageEmbedding
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    IsCompact (Set.range (S.stageEmbedding n)) :=
  isCompact_range (S.stageEmbedding_isometry n).continuous

/-- **Math.** The completed common ambient is densely exhausted by the compact
stage embeddings.  This is the ambient-density input for extending compatible
finite-radius constructions to the unbounded limit. -/
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

/-- **Math.** Any two compact stages have one pointed realization in the
completed inductive limit.  Thus all finite-radius representatives live in a
single ambient metric space, rather than in independently chosen pairwise
couplings. -/
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

/-- **Math.** The common completed realization gives an explicit upper bound
for the pointed GH distance between any two stages. -/
theorem pointedGHDistance_stage_le_common_realization
    (S : CompatiblePointedCompactSystem.{u}) (m n : ℕ) :
    pointedGHDistance
        (S.stage m).toFiniteDiameterBasedMetricSpace
        (S.stage n).toFiniteDiameterBasedMetricSpace ≤
      pointedHausdorffDist (S.stageRealization m n) :=
  pointedGHDistance_le_realization (S.stageRealization m n)

/-- **Math.** Consecutive compact stage images are nested in the completed limit. -/
theorem range_stageEmbedding_mono_succ
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ) :
    Set.range (S.stageEmbedding n) ⊆
      Set.range (S.stageEmbedding (n + 1)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨S.transition n x, ?_⟩
  have hcomm := congrFun (S.stageEmbedding_succ_comp_transition n) x
  simpa [Function.comp_apply] using hcomm

/-- **Math.** If every ball around the common basepoint is contained in a compact stage
image, then the completed inductive limit is proper.  This is the precise
radial coverage obligation needed after the compatible limits are chosen. -/
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

#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.stageEmbedding_base
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.dense_iUnion_range_stageEmbedding
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.pointedGHDistance_stage_le_common_realization
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.range_stageEmbedding_mono_succ
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.properSpace_completedLimit_of_radial_stage_coverage
