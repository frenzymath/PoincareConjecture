import PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeNearest
import PoincareConjecture.Proofs.M02.Topology.FinitePolyhedralNeighborhood
import Mathlib.Geometry.Manifold.WhitneyEmbedding








set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_embedded_three_finite_polyhedral_retract
    [T2Space M] [CompactSpace M] [Nonempty M] :
    ∃ (N : Nat)
      (K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N))),
      K.faces.Finite ∧
      ∃ (j : C(M, K.space)) (q : C(K.space, M)),
        _root_.Topology.IsClosedEmbedding j ∧ q.comp j = ContinuousMap.id M := by
  classical
  obtain ⟨N, f, hs, he, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := M)
  let e : C(M, EuclideanSpace Real (Fin N)) := ⟨f, hs.continuous⟩
  obtain ⟨r, hr, hc, hnormal⟩ :=
    exists_embedded_three_nearest_neighborhood e hs he hi
  obtain ⟨K, hfinite, hinside, hnear⟩ :=
    exists_finite_polyhedral_neighborhood (isCompact_range e.continuous) r hr
  have heK (p : M) : e p ∈ K.space :=
    interior_subset (hinside (Set.mem_range_self p))
  let j : C(M, K.space) := ⟨fun p => ⟨e p, heK p⟩,
    e.continuous.subtype_mk heK⟩
  let q : C(K.space, M) := ⟨fun z => embeddedThreeNearest e z.val,
    (hc.mono (fun z hz => hnear z hz)).domRestrict⟩
  have hfix (p : M) : q (j p) = p := by
    change embeddedThreeNearest e (e p) = p
    simpa only [add_zero] using hnormal p 0 (Submodule.zero_mem _)
      (by simpa only [norm_zero] using hr)
  refine ⟨N, K, hfinite, j, q, j.continuous.isClosedEmbedding ?_, ?_⟩
  · exact Function.LeftInverse.injective hfix
  · ext p
    exact hfix p

end PoincareConjecture.Proofs.M02.Topology
