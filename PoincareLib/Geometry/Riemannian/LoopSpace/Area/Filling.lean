import PoincareLib.Geometry.Riemannian.LoopSpace.Width

/-!
# M60 elementary filling-area comparisons

Morgan--Tian Definition 18.17 defines filling area as the infimum over
admissible spanning disks. These comparisons use an actual disk as a
nonempty witness and the nonnegative area of every admissible disk.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Filling area is at most the area of any specified admissible disk. -/
theorem m60FillingArea_le_disk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g γ) :
    fillingArea g γ ≤ D.area := by
  unfold fillingArea
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨E, rfl⟩
    exact E.area_nonnegative
  · exact ⟨D, rfl⟩

/-- A specified admissible disk makes the nonnegative area set nonempty. -/
theorem m60FillingArea_nonneg_of_disk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g γ) :
    0 ≤ fillingArea g γ := by
  unfold fillingArea
  refine le_csInf ?_ ?_
  · exact ⟨D.area, D, rfl⟩
  · rintro a ⟨E, rfl⟩
    exact E.area_nonnegative

end PoincareMT
