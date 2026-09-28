import PoincareConjecture.Definitions.M45ControlledSchedules

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M45

def InitialFlowSeed (epsilon kappa : ℝ) : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [T3Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [SecondCountableTopology M],
    ∀ N : NormalizedInitialMetric (M := M),
      ∃ F : RicciFlow 3 M (Set.Icc 0 (1 / 16 : ℝ)),
        F.metric 0 = N.metric ∧ HEq (F.connection 0) N.connection ∧
        (∀ t ∈ Set.Icc 0 (1 / 16 : ℝ), ∀ x : M,
          (F.connection t).curvatureTensorNorm x ≤ 2) ∧
        (∀ t ∈ Set.Icc 0 (1 / 16 : ℝ), ∀ x : M, ∀ r : ℝ,
          0 < r → r ≤ epsilon →
            ENNReal.ofReal (kappa * r ^ 3) ≤
              calibratedMetricVolume (F.metric t) ((F.metric t).ball x r))

def InitialFlowProducer : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 200 →
    ∃ kappa : ℝ, 0 < kappa ∧ InitialFlowSeed.{u} epsilon kappa

def InitialCaptureProducer : Prop :=
  ∀ epsilon kappa : ℝ, 0 < epsilon → epsilon ≤ 1 / 200 → 0 < kappa →
    InitialFlowSeed.{u} epsilon kappa → M45InitialSurgeryControl.{u} epsilon kappa

def NeckGluingProducer : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 200 →
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 2 ∧ M45NeckGluingProperty.{u} epsilon beta

def CapRefinementProducer : Prop :=
  ∀ {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t gamma C : ℝ} {x : StandardCapSpace},
    gamma ≤ 1 / 200 → ∀ N : StandardCapNeighborhood atlas F t gamma C x,
      Nonempty (M45StandardCapRefinement N)

end PoincareConjecture.M45
