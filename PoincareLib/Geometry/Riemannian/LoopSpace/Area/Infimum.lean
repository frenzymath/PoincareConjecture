import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Filling

/-!
# Filling-area infimum witnesses

Morgan-Tian Definition 18.17, printed p. 430: an admissible disk supplies
the finite nonempty filling class and positive-error near-minimizers.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The area range is bounded below by zero, even when empty.
Source: MT Definition 18.17, printed p. 430. -/
theorem m60DiskAreas_bddBelow (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) :
    BddBelow (Set.range (fun D : LipschitzSpanningDisk g γ => D.area)) := by
  refine ⟨0, ?_⟩
  rintro a ⟨D, rfl⟩
  exact D.area_nonnegative

/-- One admissible disk gives all the filling-data witnesses.
Source: MT Definition 18.17, printed p. 430. -/
theorem m60FillingData_of_disk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g γ) :
    FillingAreaData g γ := {
  nonempty := ⟨D⟩
  finite_witness := ⟨D, D.area, le_rfl⟩
  bounded_below := m60DiskAreas_bddBelow g γ }

/-- Every positive error admits a disk within that error of the infimum.
Source: MT Definition 18.17, printed p. 430. -/
theorem m60FillingArea_near_minimizer_of_disk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g γ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ E : LipschitzSpanningDisk g γ, E.area < fillingArea g γ + epsilon := by
  obtain ⟨a, ⟨E, rfl⟩, hE⟩ := exists_lt_of_csInf_lt
    (show (Set.range (fun E : LipschitzSpanningDisk g γ => E.area)).Nonempty
      from ⟨D.area, D, rfl⟩)
    (show fillingArea g γ < fillingArea g γ + epsilon from lt_add_of_pos_right _ hepsilon)
  exact ⟨E, hE⟩

end PoincareMT
