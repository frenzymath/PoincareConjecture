import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Theory
import PoincareLib.Geometry.CurveShortening.Deformation.Construction
import PoincareLib.Geometry.CurveShortening.Comparison.Main

/-!
# M65 Proposition 18.24 proof entry

M65 owns the swept-area deformation, good-time selection, limiting-flow
argument and terminal ODE alternative.  The predecessor record is assembled
from actual M61 and M64 outputs on the same flow and geometry.  Earlier files
remain read-only; later proof work belongs in this entry and `Proofs/M65/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- M65: Proposition 18.24 on a raw family, with exact M61 width and M64
predecessors assembled on the same flow. Source: Morgan--Tian Proposition
18.24 and Claims 19.23, 19.25--19.32, pp. 433--434 and 453--464.  The
free-loop homotopy field is the raw reformulation of the source's based
`pi_3` equality; M66 owns the later based-width transport. -/
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

/-- Concrete M61/M64 application for later consumers.  The existential keeps
the selected raw-width and comparison services explicit without putting an
admitted theorem value into a public statement type. -/
theorem m65LoopFamilyDeformation_from_predecessors :
    ∃ hM61 : M61RawWidthCore.{u}, ∃ hM64 : M64ComparisonTheory.{u},
      M65DeformationTheory hM61 hM64 := by
  let hM61 : M61RawWidthCore.{u} := m65RawWidthCore_from_closed_predecessors
  exact ⟨hM61, m64AnnulusComparison_from_predecessors,
    m65LoopFamilyDeformation hM61 m64AnnulusComparison_from_predecessors⟩

end PoincareMT
