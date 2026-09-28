import PoincareConjecture.Definitions.M64Annulus












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {gamma : ContinuousMap LoopCircle M}




theorem m64RawDiskAreaRange_nonempty
    (D : M64RawSpanningDisk g gamma) :
    (m64RawDiskAreaRange g gamma).Nonempty :=
  ⟨D.area, ⟨D, rfl⟩⟩




theorem m64RawDiskAreaRange_bddBelow
    (_D : M64RawSpanningDisk g gamma) :
    BddBelow (m64RawDiskAreaRange g gamma) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨E, rfl⟩
  exact E.area_nonnegative




theorem m64RawFillingArea_nonnegative
    (_D : M64RawSpanningDisk g gamma) :
    0 ≤ m64RawFillingArea g gamma := by
  unfold m64RawFillingArea
  apply Real.sInf_nonneg
  rintro _ ⟨E, rfl⟩
  exact E.area_nonnegative




theorem m64RawDiskArea_guards
    (D : M64RawSpanningDisk g gamma) :
    (m64RawDiskAreaRange g gamma).Nonempty ∧
      BddBelow (m64RawDiskAreaRange g gamma) ∧
      0 ≤ m64RawFillingArea g gamma :=
  ⟨m64RawDiskAreaRange_nonempty D,
    m64RawDiskAreaRange_bddBelow D,
    m64RawFillingArea_nonnegative D⟩

end PoincareConjecture
