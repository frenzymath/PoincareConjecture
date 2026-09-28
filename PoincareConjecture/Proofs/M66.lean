import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Main
import PoincareConjecture.Statements.M66
import PoincareConjecture.Proofs.M61
import PoincareConjecture.Proofs.M65

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

theorem m66SmoothTimeWidthComparison
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64) :
    M66SmoothTimeTheory hM61 hM58 hM65 :=
  horizon_m66_smooth_time_theory hM61 hM58 hM65

theorem m66SmoothTimeWidthComparison_from_predecessors :
    ∃ hM61 : M61RawWidthCore.{u},
      ∃ hM58 : RepairedShortLoopTrivialityTheory.{u},
      ∃ hM64 : M64ComparisonTheory.{u},
        ∃ hM65 : M65DeformationTheory hM61 hM64,
          M66SmoothTimeTheory hM61 hM58 hM65 := by
  obtain ⟨hM61, hM64, hM65⟩ :=
    m65LoopFamilyDeformation_from_predecessors
  exact ⟨hM61, repairedShortLoopTriviality, hM64, hM65,
    m66SmoothTimeWidthComparison hM61 repairedShortLoopTriviality hM65⟩

end PoincareConjecture
