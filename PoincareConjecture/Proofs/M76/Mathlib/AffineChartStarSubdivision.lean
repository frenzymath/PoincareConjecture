import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.VertexStarChartRestriction
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {M E V : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq V]

theorem exists_finite_subdivision_affine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite) (H : K.space ≃ₜ M)
    {ι : Type*} (e : ι → OpenPartialHomeomorph M E) (U : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hUs : ∀ i, U i ⊆ (e i).source)
    (hcover : ∀ x : M, ∃ i, x ∈ U i) (a : ι → V →ᴬ[ℝ] E)
    (ha : ∀ i, ∀ y : K.space, H y ∈ U i → e i (H y) = a i y) :
    ∃ L : SimplicialComplex ℝ V, L.faces.Finite ∧ L.IsSubdivision K ∧
      ∀ p : V, {p} ∈ L.faces → ∃ i,
        InjOn (a i) (L.closedFaceStar {p}).space ∧
        a i p ∈ interior (a i '' (L.closedFaceStar {p}).space) := by
  classical
  let W : ι → Set K.space := fun i => H ⁻¹' U i
  have hW (i : ι) : IsOpen (W i) := (hU i).preimage H.continuous
  have hWcover (y : K.space) : ∃ i, y ∈ W i := hcover (H y)
  obtain ⟨L, hL, hLK, hstars⟩ := K.exists_finite_subdivision_stars hK W hW hWcover
  let H' : L.space ≃ₜ M := (Homeomorph.setCongr hLK.space_eq).trans H
  refine ⟨L, hL, hLK, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := hstars p hp
  have hcore (y : L.space) (hy : (y : V) ∈ (L.closedFaceStar {p}).space) :
      H' y ∈ U i := hi ⟨y, hLK.space_eq ▸ y.property⟩ hy
  let d : OpenPartialHomeomorph L.space E := H'.toOpenPartialHomeomorph.trans (e i)
  have hsource (y : L.space) (hy : (y : V) ∈ (L.closedFaceStar {p}).space) :
      y ∈ d.source := ⟨mem_univ y, hUs i (hcore y hy)⟩
  have heq (y : L.space) (hy : (y : V) ∈ (L.closedFaceStar {p}).space) :
      d y = a i y := ha i ⟨y, hLK.space_eq ▸ y.property⟩ (hcore y hy)
  exact ⟨i, L.injOn_and_interior_closedStar_of_chart hL hp d (a i) hsource heq⟩

end Geometry.SimplicialComplex
