import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonUniqueness
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonAnnuli
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformCompactChordPackage
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonChordLength
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledPolygon












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture





theorem m64_uniform_compact_approximation
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    (X : Set (C1FreeLoopSpace (M := M))) (hX : IsCompact X)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ N0 : ℕ, 0 < N0 ∧
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
              0 ≤ A.area ∧ A.area < zeta := by
  obtain ⟨NU, hNU, huniq⟩ :=
    m64_uniform_compact_sampled_polygon_unique g D hcompact X hX
  obtain ⟨NC, _hNC, hchord⟩ :=
    m64_uniform_compact_chord_of_compact (g := g) hcompact X hX zeta hzeta
  obtain ⟨NA, _hNA, hannuli⟩ :=
    m64_uniform_compact_sampled_polygon_annuli g D hcompact X hX hzeta
  refine ⟨max NU (max NC NA), hNU.trans_le (le_max_left _ _), ?_⟩
  intro N hN0N gamma hgamma
  have hNUN : NU ≤ N := (le_max_left _ _).trans hN0N
  have hNCN : NC ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN0N)
  have hNAN : NA ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN0N)
  have hN : 0 < N := hNU.trans_le hNUN
  obtain ⟨polygon, hsampled, hboundary⟩ :=
    m64_sampled_polygon_exists (g := g) (D := D) hcompact gamma N hN
  refine ⟨polygon, hsampled, ?_, hboundary, ?_, ?_⟩
  · intro other hother
    exact huniq N hNUN gamma hgamma polygon other hsampled hother
  · rw [m64PolygonLength_eq_sampled_chord_sum polygon hN (periodicFreeLoop gamma)
      (Proofs.M58.periodic_periodicFreeLoop gamma)
      (Proofs.M58.contMDiff_periodicFreeLoop gamma) hsampled]
    exact hchord N hNCN gamma hgamma
  · exact hannuli N hNAN gamma hgamma polygon hsampled

end PoincareConjecture
