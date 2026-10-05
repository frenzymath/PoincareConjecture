import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.FineSimplicialSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.VertexStarChartRestriction
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Closed vertex stars inside actual affine chart cores

Subdivide a finite carrier until every closed vertex star lies
inside an open chart core with a known ambient affine formula.
The same formula is injective on the star and sends its vertex
into the interior of its image. See Cairns 1940, pp. 798--799,
Hamilton 1976, p. 69 and M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {M E V : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq V]

/-- Actual affine formulas on an open chart-core cover give
a finite subdivision with affine Brouwer vertex stars. The
whole closed star lies in the corresponding source, so the
chart restriction proves both injection and interior image.
See Cairns pp. 798--799 and M76 derivation 258. -/
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
