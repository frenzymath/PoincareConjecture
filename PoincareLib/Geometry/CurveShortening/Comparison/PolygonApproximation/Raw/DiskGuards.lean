import PoincareLib.Geometry.CurveShortening.Comparison.Annulus

/-!
# Guards for the raw disk infimum

The raw filling infimum is only used after a raw disk witness is available.
This file packages the corresponding range nonemptiness, lower bound, and
nonnegative infimum facts.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {gamma : ContinuousMap LoopCircle M}

/-- An actual raw spanning disk makes its area range nonempty. Source: Auxiliary step for MT
Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawDiskAreaRange_nonempty
    (D : M64RawSpanningDisk g gamma) :
    (m64RawDiskAreaRange g gamma).Nonempty :=
  ⟨D.area, ⟨D, rfl⟩⟩

/-- Nonnegative areas bound the raw disk area range below. Source: Auxiliary step for MT
Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawDiskAreaRange_bddBelow
    (_D : M64RawSpanningDisk g gamma) :
    BddBelow (m64RawDiskAreaRange g gamma) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨E, rfl⟩
  exact E.area_nonnegative

/-- A supplied raw disk guards nonnegativity of the filling-area infimum. Source: Auxiliary
step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawFillingArea_nonnegative
    (_D : M64RawSpanningDisk g gamma) :
    0 ≤ m64RawFillingArea g gamma := by
  unfold m64RawFillingArea
  apply Real.sInf_nonneg
  rintro _ ⟨E, rfl⟩
  exact E.area_nonnegative

/-- Retain nonemptiness, boundedness below, and nonnegativity for the actual raw filling
class. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453;
project construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawDiskArea_guards
    (D : M64RawSpanningDisk g gamma) :
    (m64RawDiskAreaRange g gamma).Nonempty ∧
      BddBelow (m64RawDiskAreaRange g gamma) ∧
      0 ≤ m64RawFillingArea g gamma :=
  ⟨m64RawDiskAreaRange_nonempty D,
    m64RawDiskAreaRange_bddBelow D,
    m64RawFillingArea_nonnegative D⟩

end PoincareMT
