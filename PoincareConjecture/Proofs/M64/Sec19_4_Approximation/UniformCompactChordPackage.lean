import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformCompactChordLength

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

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

end PoincareConjecture
