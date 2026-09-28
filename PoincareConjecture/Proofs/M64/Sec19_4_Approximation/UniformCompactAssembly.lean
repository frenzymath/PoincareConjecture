import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonChordLength
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

structure M64UniformCompactPackage where
  chord : ∀ X : Set (C1FreeLoopSpace (M := M)), IsCompact X →
    ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        let chord := ∑ j : Fin N,
          (g.edist
            (periodicFreeLoop gamma (m63CellLeft N j))
            (periodicFreeLoop gamma (m63CellLeft N (finRotate N j)))).toReal
        0 ≤ freeLoopLength g gamma - chord ∧
          freeLoopLength g gamma - chord < zeta
  polygon : ∀ X : Set (C1FreeLoopSpace (M := M)), IsCompact X →
    ∀ zeta : ℝ, 0 < zeta → ∀ N : ℕ, 0 < N →
      ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        ∃ polygon : M63GeodesicPolygon g D N,
          M64SampledPolygon gamma polygon ∧
          (∀ other : M63GeodesicPolygon g D N,
            M64SampledPolygon gamma other →
              ∀ x, other.map x = polygon.map x) ∧
          Nonempty (M64PolygonBoundary polygon) ∧
          ∃ A : M64Annulus g (periodicFreeLoop gamma) polygon.map,
            M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
              0 ≤ A.area ∧ A.area < zeta

theorem M64UniformCompactPackage.uniform_compact
    (P : M64UniformCompactPackage (M := M) (g := g) (D := D)) :
    ∀ X : Set (C1FreeLoopSpace (M := M)), IsCompact X →
      ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
        ∀ N : ℕ, N0 ≤ N → ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
          ∃ polygon : M63GeodesicPolygon g D N,
            M64SampledPolygon gamma polygon ∧
            (∀ other : M63GeodesicPolygon g D N,
              M64SampledPolygon gamma other →
                ∀ x, other.map x = polygon.map x) ∧
            Nonempty (M64PolygonBoundary polygon) ∧
            (0 ≤ freeLoopLength g gamma - m64PolygonLength polygon ∧
              freeLoopLength g gamma - m64PolygonLength polygon < zeta) ∧
            ∃ A : M64Annulus g (periodicFreeLoop gamma) polygon.map,
              M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
                0 ≤ A.area ∧ A.area < zeta := by
  intro X hX zeta hzeta
  obtain ⟨N0, hN0, hchord⟩ := P.chord X hX zeta hzeta
  refine ⟨N0, hN0, ?_⟩
  intro N hN0N gamma hgammaX
  have hN : 0 < N := lt_of_lt_of_le hN0 hN0N
  obtain ⟨polygon, hsampled, hunique, hboundary, hannulus⟩ :=
    P.polygon X hX zeta hzeta N hN gamma hgammaX
  have hlength := m64PolygonLength_eq_sampled_chord_sum polygon hN
    (periodicFreeLoop gamma)
    (Proofs.M58.periodic_periodicFreeLoop gamma)
    (Proofs.M58.contMDiff_periodicFreeLoop gamma)
    hsampled
  obtain ⟨hchord0, hchordlt⟩ := hchord N hN0N gamma hgammaX
  refine ⟨polygon, hsampled, hunique, hboundary, ?_, hannulus⟩
  constructor
  · rw [hlength]
    exact hchord0
  · rw [hlength]
    exact hchordlt

end PoincareConjecture
