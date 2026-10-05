import PoincareLib.Geometry.Spacetime.OrdinaryProduct
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Interval-aware M11 conclusion

The current Mapher conclusion adds the selected interval restriction
local-diffeomorphism field to the earlier Horizon carrier record.  This file
keeps that source-level extension separate from the construction proofs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]

structure GeneralizedFlowCarrierConclusionWithInterval
    (A : AdaptedMetricAtlas n X) extends GeneralizedFlowCarrierConclusion A where
  interval_localDiffeomorph : ∀ (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain),
    IsOpen {t : K.domain | t.val ∈ L.domain} →
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞
      (spacetimeIntervalInclusion (timeIntervals.interval L)
        (timeIntervals.interval K) h)

namespace GeneralizedFlowCarrierConclusionWithInterval

variable {A : AdaptedMetricAtlas n X}

abbrev toConclusion (R : GeneralizedFlowCarrierConclusionWithInterval A) :
    GeneralizedFlowCarrierConclusion A :=
  R.toGeneralizedFlowCarrierConclusion

@[simp] theorem toConclusion_timeIntervals
    (R : GeneralizedFlowCarrierConclusionWithInterval A) :
    R.toConclusion.timeIntervals = R.timeIntervals := rfl

@[simp] theorem toConclusion_spacetime
    (R : GeneralizedFlowCarrierConclusionWithInterval A) :
    R.toConclusion.spacetime = R.spacetime := rfl

end GeneralizedFlowCarrierConclusionWithInterval

abbrev GeneralizedFlowCarrierRealization (A : AdaptedMetricAtlas n X) :=
  GeneralizedFlowCarrierConclusionWithInterval A

structure GeneralizedSpacetimeRealizationTheory (n : ℕ) : Prop
    extends GeneralizedSpacetimeGeometryTheory.{u} n where
  realize_with_interval : ∀ (X : Type u) [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X]
    (A : AdaptedMetricAtlas n X),
    Nonempty (GeneralizedFlowCarrierConclusionWithInterval A)

namespace GeneralizedSpacetimeRealizationTheory

variable {n : ℕ}

abbrev toGeometryTheory
    (H : GeneralizedSpacetimeRealizationTheory.{u} n) :
    GeneralizedSpacetimeGeometryTheory.{u} n :=
  H.toGeneralizedSpacetimeGeometryTheory

theorem realize_projection
    (H : GeneralizedSpacetimeRealizationTheory.{u} n)
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] (A : AdaptedMetricAtlas n X) :
    Nonempty (GeneralizedFlowCarrierConclusion A) := by
  obtain ⟨R⟩ := H.realize_with_interval X A
  exact ⟨R.toConclusion⟩

end GeneralizedSpacetimeRealizationTheory

end PoincareMT
