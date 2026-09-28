import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledPolygon
import PoincareConjecture.Statements.M64Approximation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

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

end PoincareConjecture
