import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Uniform.CompactChordLength

/-!
# The compact-family chord package

The metric-free chord estimate applies directly to the subtype of an
arbitrary compact set of `C1FreeLoopSpace`.  This adapter has exactly the
chord shape consumed by `M64UniformCompactPackage`; polygon and annulus data
remain separate M64 witnesses.

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
  {g : RiemannianMetric 3 M}

/-- Transfer the uniform sampled-chord estimate to the intrinsic C1 topology on a compact
loop set. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_uniform_compact_chord_of_compact
    (hcompact : IsCompact (univ : Set M))
    (X : Set (C1FreeLoopSpace (M := M))) (hX : IsCompact X) :
    ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        let chord := ∑ j : Fin N,
          (g.edist
            (periodicFreeLoop gamma (m63CellLeft N j))
            (periodicFreeLoop gamma (m63CellLeft N (finRotate N j)))).toReal
        0 ≤ freeLoopLength g gamma - chord ∧
          freeLoopLength g gamma - chord < zeta := by
  intro zeta hzeta
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨N0, hN0, hchord⟩ :=
    m64_exists_uniform_sampled_chord_length (g := g) hcompact
      (Z := X) (fun gamma : X => gamma.1) continuous_subtype_val hzeta
  refine ⟨N0, hN0, ?_⟩
  intro N hN gamma hgamma
  simpa only using hchord N hN ⟨gamma, hgamma⟩

end PoincareMT
