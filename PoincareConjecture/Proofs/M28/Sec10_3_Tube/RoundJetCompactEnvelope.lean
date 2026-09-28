import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer
import PoincareConjecture.Proofs.M03.MetricInverse











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology Uniformity

noncomputable section

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds

abbrev JetE := EuclideanSpace ℝ (Fin 3)
abbrev JetMetric := MetricCoefficient 3



local instance jetMetricNorm : NormedAddCommGroup JetMetric :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jetMetricSpace : NormedSpace ℝ JetMetric :=
  ContinuousLinearMap.toNormedSpace

abbrev JetFirst := JetE →L[ℝ] JetMetric
local instance jetFirstNorm : NormedAddCommGroup JetFirst :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jetFirstSpace : NormedSpace ℝ JetFirst :=
  ContinuousLinearMap.toNormedSpace

abbrev JetSecond := JetE →L[ℝ] JetFirst
local instance jetSecondNorm : NormedAddCommGroup JetSecond :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jetSecondSpace : NormedSpace ℝ JetSecond :=
  ContinuousLinearMap.toNormedSpace

local instance jetFirstAdd : AddCommMonoid JetFirst :=
  jetFirstNorm.toAddCommMonoid
local instance jetSecondAdd : AddCommMonoid JetSecond :=
  jetSecondNorm.toAddCommMonoid
local instance jetFirstModule : Module ℝ JetFirst := jetFirstSpace.toModule
local instance jetSecondModule : Module ℝ JetSecond := jetSecondSpace.toModule
local instance jetMetricFinite : Module.Finite ℝ JetMetric :=
  ContinuousLinearMap.instModuleFinite
local instance jetFirstFinite : Module.Finite ℝ JetFirst :=
  ContinuousLinearMap.instModuleFinite
local instance jetSecondFinite : Module.Finite ℝ JetSecond :=
  ContinuousLinearMap.instModuleFinite
local instance jetTailFinite : Module.Finite ℝ (JetFirst × JetSecond) :=
  Module.Finite.prod
local instance jetAllFinite : Module.Finite ℝ (JetMetric × (JetFirst × JetSecond)) :=
  Module.Finite.prod
local instance jetAllProper : ProperSpace (MetricTwoJet 3) :=
  FiniteDimensional.proper ℝ _

noncomputable def normalizedEuclideanMetric : JetMetric :=
  (innerSL ℝ).toLinearMap.toContinuousLinearMap

def roundJetBoundSet (B₁ B₂ : ℝ) : Set (MetricTwoJet 3) :=
  {J | J.1 = normalizedEuclideanMetric ∧
    ‖J.2.1‖ ≤ B₁ ∧ ‖J.2.2‖ ≤ B₂}

def roundJetScalarSixSet (B₁ B₂ : ℝ) : Set (MetricTwoJet 3) :=
  {J | J ∈ roundJetBoundSet B₁ B₂ ∧ jetScalarCurvature J = 6}

theorem normalizedEuclideanMetric_isInvertible :
    normalizedEuclideanMetric.IsInvertible := by
  apply PoincareConjecture.Proofs.M03.isInvertible_bilinear_of_pos
  intro v hv
  change inner ℝ v v > 0
  exact real_inner_self_pos.mpr hv

theorem isCompact_roundJetBoundSet (B₁ B₂ : ℝ) :
    IsCompact (roundJetBoundSet B₁ B₂) := by
  have hprod : IsCompact
      (({normalizedEuclideanMetric} : Set JetMetric) ×ˢ
        (Metric.closedBall (0 : JetFirst) B₁ ×ˢ
          Metric.closedBall (0 : JetSecond) B₂)) := by
    exact isCompact_singleton.prod
      ((isCompact_closedBall (0 : JetFirst) B₁).prod
        (isCompact_closedBall (0 : JetSecond) B₂))
  have heq : roundJetBoundSet B₁ B₂ =
      (({normalizedEuclideanMetric} : Set JetMetric) ×ˢ
        (Metric.closedBall (0 : JetFirst) B₁ ×ˢ
          Metric.closedBall (0 : JetSecond) B₂)) := by
    ext J
    simp [roundJetBoundSet, Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact hprod

theorem roundJetScalarSixSet_subset_boundSet (B₁ B₂ : ℝ) :
    roundJetScalarSixSet B₁ B₂ ⊆ roundJetBoundSet B₁ B₂ := by
  intro J hJ
  exact hJ.1

theorem exists_roundJet_scalar_uniform_modulus
    (B₁ B₂ : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ J ∈ roundJetScalarSixSet B₁ B₂,
        ∀ L : MetricTwoJet 3, dist L J < eta →
          |jetScalarCurvature L - 6| < delta := by
  have hcompact : IsCompact (roundJetBoundSet B₁ B₂) :=
    isCompact_roundJetBoundSet B₁ B₂
  have hinvertible : ∀ J ∈ roundJetBoundSet B₁ B₂,
      J.1.IsInvertible := by
    intro J hJ
    rw [hJ.1]
    exact normalizedEuclideanMetric_isInvertible
  obtain ⟨eta, heta, hmod⟩ :=
    exists_jetScalarCurvature_uniform_modulus
      (K := roundJetBoundSet B₁ B₂) hcompact hinvertible hdelta
  refine ⟨eta, heta, ?_⟩
  intro J hJ L hLJ
  have hbase := hmod J (roundJetScalarSixSet_subset_boundSet B₁ B₂ hJ)
    L hLJ
  have hsix : jetScalarCurvature J = 6 := hJ.2
  simpa [hsix] using hbase

end PoincareConjecture.M28.tube
