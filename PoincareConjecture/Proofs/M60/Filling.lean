import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]


theorem m60FillingArea_le_disk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g γ) :
    fillingArea g γ ≤ D.area := by
  unfold fillingArea
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨E, rfl⟩
    exact E.area_nonnegative
  · exact ⟨D, rfl⟩


theorem m60FillingArea_nonneg_of_disk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g γ) :
    0 ≤ fillingArea g γ := by
  unfold fillingArea
  refine le_csInf ?_ ?_
  · exact ⟨D.area, D, rfl⟩
  · rintro a ⟨E, rfl⟩
    exact E.area_nonnegative

end PoincareConjecture
