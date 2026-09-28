import PoincareConjecture.Definitions.M65
import PoincareConjecture.Statements.M61Width
import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M65Predecessors (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁) where
  width : M61FamilyWidthProperties (P.flow.metric t₀) P.family
  m64 : M64ThreeDimensionalFlowConclusion P.flow

structure M65Conclusion (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁)
    (H : M65Predecessors M P) where
  deformation : ∀ zeta : ℝ, 0 < zeta →
    Nonempty (M65DeformedFamily M P zeta)

noncomputable def m65PredecessorsFromServices
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁) :
    M65Predecessors M P := by
  letI : T2Space M := P.hausdorff
  letI : SecondCountableTopology M := P.second_countable
  let A : M64ThreeDimensionalFlowConclusion P.flow :=
    Classical.choice (hM64.2.2.2 M t₀ t₁ P.flow P.compact)
  refine
    { width := hM61.family (P.flow.metric t₀) P.compact P.family P.family_null
      m64 := A }

def M65DeformationTheory
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u}) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁),
    Nonempty (M65Conclusion M P (m65PredecessorsFromServices hM61 hM64 P))

end PoincareConjecture
