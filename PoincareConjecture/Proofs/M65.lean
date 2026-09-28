import PoincareConjecture.Statements.M65
import PoincareConjecture.Proofs.M65.Construction
import PoincareConjecture.Proofs.M64

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m65LoopFamilyDeformation
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u}) :
    M65DeformationTheory hM61 hM64 := by
  have construction : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁),
      ∀ H : M65Predecessors M P, Nonempty (M65Conclusion M P H) := by
    exact m65Construction hM61 hM64
  intro M _ _ _ t₀ t₁ P
  exact construction M P (m65PredecessorsFromServices hM61 hM64 P)

theorem m65LoopFamilyDeformation_from_predecessors :
    ∃ hM61 : M61RawWidthCore.{u}, ∃ hM64 : M64ComparisonTheory.{u},
      M65DeformationTheory hM61 hM64 := by
  let hM61 : M61RawWidthCore.{u} := m65RawWidthCore_from_closed_predecessors
  exact ⟨hM61, m64AnnulusComparison_from_predecessors,
    m65LoopFamilyDeformation hM61 m64AnnulusComparison_from_predecessors⟩

end PoincareConjecture
