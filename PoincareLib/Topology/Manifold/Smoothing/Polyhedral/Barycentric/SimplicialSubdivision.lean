import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineOnFaces

/-!
# Subdivisions of geometric simplicial complexes

A subdivision has the same carrier and every fine simplex lies
inside a coarse simplex. See Hudson 1969, Chapter 1, Section 2,
p. 5, Hamilton 1976, pp. 68--69 and M76 derivation 73.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first complex subdivides the second when their carriers
agree and its simplices refine the latter's simplices. This is
Hudson's definition, p. 5; see M76 derivation 73. -/
structure IsSubdivision (K L : SimplicialComplex ℝ E) : Prop where
  /-- Subdivision preserves the carrier; Hudson p. 5. -/
  space_eq : K.space = L.space
  /-- Every fine simplex is contained in a coarse simplex; Hudson p. 5. -/
  face_subset : ∀ s ∈ K.faces, ∃ t ∈ L.faces,
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)

/-- A complex is a subdivision of itself. See Hudson p. 5
and M76 derivation 73. -/
theorem IsSubdivision.refl (K : SimplicialComplex ℝ E) : K.IsSubdivision K :=
  ⟨rfl, fun s hs => ⟨s, hs, Subset.rfl⟩⟩

/-- Successive subdivisions compose. See Hudson p. 5 and
M76 derivation 73. -/
theorem IsSubdivision.trans {K L N : SimplicialComplex ℝ E}
    (hKL : K.IsSubdivision L) (hLN : L.IsSubdivision N) : K.IsSubdivision N := by
  refine ⟨hKL.space_eq.trans hLN.space_eq, fun s hs => ?_⟩
  obtain ⟨t, ht, hst⟩ := hKL.face_subset s hs
  obtain ⟨u, hu, htu⟩ := hLN.face_subset t ht
  exact ⟨u, hu, hst.trans htu⟩

/-- A subdivision preserves every coarse face-affine formula.
See Hudson p. 5, Hamilton pp. 68--69 and M76 derivation 73. -/
theorem IsSubdivision.affineOnFaces {K L : SimplicialComplex ℝ E}
    (hKL : K.IsSubdivision L) {f : E → F} (hf : L.AffineOnFaces f) : K.AffineOnFaces f :=
  hf.of_face_containment hKL.face_subset

end Geometry.SimplicialComplex
