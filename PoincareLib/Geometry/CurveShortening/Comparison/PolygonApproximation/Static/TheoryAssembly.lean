import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Sampled.Polygon
import PoincareLib.Geometry.CurveShortening.Comparison.ApproximationTheory

/-!
# Static approximation assembly

The pointwise sampled polygon and exact length fields are proved from the
closed M63 polygon supplier.  The compact-family and raw-family fields carry
the additional short-annulus and filling witnesses required by M64, so this
file keeps those two genuine producers explicit while assembling the record.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

/-- Assemble the full static theory from the two genuinely M64-specific suppliers and the
closed pointwise polygon construction. Source: Auxiliary step for MT Definition 19.18 and
Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64StaticApproximationTheory_of_suppliers
    (hcompact : IsCompact (univ : Set M))
    (huniform : ∀ X : Set (C1FreeLoopSpace (M := M)), IsCompact X →
      ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
        ∀ N : ℕ, N0 ≤ N → ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
          ∃ polygon : M63GeodesicPolygon g D N,
            M64SampledPolygon gamma polygon ∧
            (∀ other : M63GeodesicPolygon g D N, M64SampledPolygon gamma other →
              ∀ x, other.map x = polygon.map x) ∧
            Nonempty (M64PolygonBoundary polygon) ∧
            (0 ≤ freeLoopLength g gamma - m64PolygonLength polygon ∧
              freeLoopLength g gamma - m64PolygonLength polygon < zeta) ∧
            ∃ A : M64Annulus g (periodicFreeLoop gamma) polygon.map,
              M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
                0 ≤ A.area ∧ A.area < zeta)
    (hraw : ∀ Gamma : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)), M61NullFamily Gamma →
      ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ A : M64RawFamilyApproximation g D Gamma zeta, A.count = N) :
    M64StaticApproximationTheory g D := by
  obtain ⟨hsampled, hlength⟩ := m64_static_polygon_fields (g := g) (D := D) hcompact
  exact {
    sampled_exists := hsampled
    polygon_length := hlength
    uniform_compact := huniform
    raw_family := hraw }

end PoincareMT
