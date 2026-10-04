import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FineFacesNearCompact
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedronNeighborhoodRetraction

/-!

# Full subcomplexes with confined incident faces

First make all faces meeting the prescribed finite polyhedron
small. Align that polyhedron as an exact subcomplex and then
make it full by barycentric subdivision. Every final incident
face remains in the same prescribed compact neighborhood.
See Hudson 1969, pp. 8--9, 12--19, Hatcher, Theorem 3.1,
p. 45 and M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite polyhedron becomes an exact full subcomplex
whose entire incident faces lie in a compact subset of any
prescribed relative open neighborhood. The original ambient
carrier is unchanged. See Hudson pp. 8--9, 12--19 and
M76 derivation 270. -/
theorem exists_full_subcomplex_confined_neighborhood
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (hJK : J.space ⊆ K.space) {O : Set K.space} (hO : IsOpen O)
    (hJO : ∀ x : K.space, (x : E) ∈ J.space → x ∈ O) :
    ∃ (R L : SimplicialComplex ℝ E) (P : Set E),
      R.faces.Finite ∧ R.IsSubdivision K ∧ L ≤ R ∧ L.space = J.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) ∧
      IsCompact P ∧ J.space ⊆ P ∧ P ⊆ Subtype.val '' O ∧
      ∀ s ∈ R.faces, (convexHull ℝ (s : Set E) ∩ J.space).Nonempty →
        convexHull ℝ (s : Set E) ⊆ P := by
  classical
  obtain ⟨T, P, hT, hTK, hP, hJP, hPO, hfaces⟩ :=
    K.exists_subdivision_faces_near_compact hK (J.isCompact_space_of_finite hJ) hJK hO hJO
  obtain ⟨R, L, hR, hRT, hLR, hLJ⟩ :=
    T.exists_subdivision_with_polyhedron_subcomplex J hT hJ
      (fun x hx => hTK.space_eq.symm ▸ hJK hx)
  let : Fintype R.faces := hR.fintype
  let : Fintype L.faces := (hR.subset hLR).fintype
  have hsub := R.barycentricSubdivision_isSubdivision.trans hRT
  refine ⟨R.barycentricSubdivision, L.barycentricSubdivision, P,
    R.barycentricSubdivision_finite, hsub.trans hTK,
    L.barycentricSubdivision_mono hLR,
    L.barycentricSubdivision_isSubdivision.space_eq.trans hLJ,
    fun s hs hv => R.barycentricSubdivision_full hLR hs hv,
    hP, hJP, hPO, ?_⟩
  intro s hs hmeet
  obtain ⟨t, ht, hst⟩ := hsub.face_subset s hs
  have htmeet : (convexHull ℝ (t : Set E) ∩ J.space).Nonempty := by
    obtain ⟨x, hxs, hxJ⟩ := hmeet
    exact ⟨x, hst hxs, hxJ⟩
  exact hst.trans (hfaces t ht htmeet)

end Geometry.SimplicialComplex
