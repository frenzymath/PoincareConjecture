import PoincareLib.Topology.Manifold.Smoothing.Dehn.Topology.Mathlib.GeometricOpenStars
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.FineSimplicialSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineFaceMaps

/-!
# Actual simplicial approximation retaining every containing target face

Whole closed-star control selects actual target vertices. Interpolation
on the actual fine source complex then preserves every original target
face containing the image point, including all marked subcomplexes.
See Hatcher, Theorem 3.1, p. 45, and the explicit PL reconstruction in
Dehn derivations 022 section 3 and 023 section 2.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- Construct one finite source subdivision and an actual face-affine
map preserving every target face containing each original image point.
The entire carrier and all target subcomplexes are retained.
See Dehn derivation 023, section 2. -/
theorem exists_carrier_simplicial_approximation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (P : SimplicialComplex ℝ G) (hP : P.faces.Finite)
    (f : C(K.space, P.space)) :
    ∃ (g : E → G) (L : SimplicialComplex ℝ E),
      L.faces.Finite ∧ L.IsSubdivision K ∧ L.AffineOnFaces g ∧
      ∀ (x : K.space) (t : Finset G), t ∈ P.faces →
        (f x : G) ∈ convexHull ℝ (t : Set G) → g x ∈ convexHull ℝ (t : Set G) := by
  classical
  let : Fintype P.vertices := (P.finite_vertices_of_finite_faces hP).fintype
  let U : P.vertices → Set K.space := fun i => f ⁻¹' P.geometricOpenVertexStar i
  have hU (i : P.vertices) : IsOpen (U i) :=
    (P.isOpen_geometricOpenVertexStar i).preimage f.continuous
  have hcover (x : K.space) : ∃ i, x ∈ U i := P.exists_mem_geometricOpenVertexStar (f x)
  obtain ⟨L, hL, hLK, hstars⟩ := K.exists_finite_subdivision_stars hK U hU hcover
  choose a ha using fun p : L.vertices => hstars p.val p.property
  let v : E → G := Function.extend ((↑) : L.vertices → E)
    (fun p => (a p : G)) (fun _ => 0)
  obtain ⟨g, hg, hgv⟩ := L.exists_affineOnFaces_eqOn_vertices v
  have hga (p : L.vertices) : g p = (a p : G) :=
    (hgv p.property).trans (Subtype.val_injective.extend_apply _ _ p)
  refine ⟨g, L, hL, hLK, hg, ?_⟩
  intro x t ht hxt
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hLK.space_eq.symm.subset x.property)
  apply hg.mapsTo_convexHull hs _ hxs
  rintro y ⟨p, hp, rfl⟩
  have hpL : p ∈ L.vertices := L.down_closed hs
    (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_nonempty p)
  let pv : L.vertices := ⟨p, hpL⟩
  have hxstar : x.val ∈ (L.closedFaceStar {p}).space := by
    apply (L.closedFaceStar {p}).convexHull_subset_space (s := s) _ hxs
    refine ⟨hs, ?_⟩
    simpa only [Finset.singleton_union, Finset.insert_eq_of_mem hp] using hs
  change g pv ∈ t
  rw [hga pv]
  exact P.mem_face_of_mem_geometricOpenVertexStar ht hxt (ha pv x hxstar)

end Geometry.SimplicialComplex
