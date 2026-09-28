import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.FrontierStarCoordinates
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Planar.PairedTriangleDeterminants

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_frontier_edge_opposite_determinants
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)))
    (b : Module.Basis (Fin 3) ℝ V3)
    {s t u : Finset E} (hs : s ∈ A.faces) (ht : t ∈ A.faces) (hu : u ∈ A.faces)
    (hsc : s.card = 2) (htc : t.card = 3) (huc : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hp0 : p 0 ∈ s) (hpt : ∀ i, p i ∈ t)
    (hsp : ∀ x ∈ s, x = p 0 ∨ x = p 1) :
    ∃ (C : OpenPartialHomeomorph X V3) (ell : V3 →ᴬ[ℝ] ℝ) (n : V3) (q : E),
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (A.closedStar (p 0)).space C.source ∧
      (A.closedStar (p 0)).AffineOnFaces (C ∘ g) ∧
      ell.contLinear n = 1 ∧
      (∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)) ∧
      q ∉ s ∧ u = insert q s ∧
      b.det ![C (g (p 1)) - C (g (p 0)), C (g (p 2)) - C (g (p 0)), n] *
        b.det ![C (g (p 1)) - C (g (p 0)), C (g q) - C (g (p 0)), n] < 0 := by
  have hpA : p 0 ∈ A.vertices := A.mem_vertices.mpr
    (A.down_closed hs (Finset.singleton_subset_iff.mpr hp0) (Finset.singleton_nonempty _))
  obtain ⟨C, ell, n, hcompat, hsource, haff, hi, hn, hside, hplane⟩ :=
    exists_frontier_subcomplex_star_coordinates e K A hAK g N hgi hfront hstars (p 0) hpA
  have hs' : s ∈ (A.closedStar (p 0)).faces :=
    ⟨hs, by simpa only [Finset.insert_eq_of_mem hp0] using hs⟩
  have ht' : t ∈ (A.closedStar (p 0)).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hp0)] using ht⟩
  have hu' : u ∈ (A.closedStar (p 0)).faces :=
    ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hp0)] using hu⟩
  obtain ⟨q, hqs, hqu, hdet⟩ := haff.exists_opposite_triangle_determinants
    (A.closedStar (p 0)) (C ∘ g) hi b ell n hn hplane
    hs' ht' hu' hsc htc huc hst hsu htu p hp hpt hsp
  refine ⟨C, ell, n, q, hcompat, hsource, haff, hn, hside, hqs, ?_, hdet⟩
  convert! hqu

end PoincareConjecture.M76
