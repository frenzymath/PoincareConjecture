import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineOnFaces
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineInterpolation

/-!
# Extension and uniqueness of simplicial vertex maps

Vertex values determine a face-affine map on its carrier. In a
finite-dimensional ambient space they always extend to such a map, using
affine interpolation and the common-face intersection axiom. This is the
simplex-map construction used in Hamilton 1976, pp. 64, 69, and Cairns 1940,
pp. 797--798. See M76 derivation 12.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

/-- Two face-affine maps agreeing on vertices agree on the whole carrier.
See the simplex correspondences of Cairns pp. 797--798 and M76 derivation 12. -/
theorem AffineOnFaces.eqOn_of_eqOn_vertices (hf : K.AffineOnFaces f)
    (hg : K.AffineOnFaces g) (hfg : EqOn f g K.vertices) : EqOn f g K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg s hs
  have hv : (s : Set E) ⊆ K.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs
  have hab : EqOn a.toAffineMap b.toAffineMap (s : Set E) := by
    intro y hy
    exact (ha (subset_convexHull ℝ _ hy)).symm.trans
      ((hfg (hv hy)).trans (hb (subset_convexHull ℝ _ hy)))
  exact (ha hxs).trans
    ((AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hxs)).trans (hb hxs).symm)

variable [FiniteDimensional ℝ E]

/-- Any vertex assignment extends to a function affine on each face.
Continuity on the carrier follows under local finiteness from
`AffineOnFaces.continuousOn_of_locallyFinite`. See Hamilton p. 64,
Cairns pp. 797--798 and M76 derivation 12. -/
theorem exists_affineOnFaces_eqOn_vertices (K : SimplicialComplex ℝ E) (v : E → F) :
    ∃ f : E → F, K.AffineOnFaces f ∧ EqOn f v K.vertices := by
  classical
  choose a ha using fun s : K.faces => (K.indep s.property).exists_continuousAffineMap_eqOn v
  have hcompat (s t : K.faces) : EqOn (a s) (a t)
      (convexHull ℝ (s.val : Set E) ∩ convexHull ℝ (t.val : Set E)) := by
    have hab : EqOn (a s).toAffineMap (a t).toAffineMap
        ((s.val : Set E) ∩ (t.val : Set E)) := by
      intro x hx
      exact (ha s hx.1).trans (ha t hx.2).symm
    intro x hx
    rw [K.convexHull_inter_convexHull s.property t.property] at hx
    exact AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hx)
  choose s hs hxs using fun x : K.space => mem_space_iff.mp x.property
  let face : K.space → K.faces := fun x => ⟨s x, hs x⟩
  have hface (x : K.space) : (x : E) ∈ convexHull ℝ ((face x).val : Set E) := hxs x
  let f : E → F := fun x => if hx : x ∈ K.space then a (face ⟨x, hx⟩) x else 0
  have hformula (t : K.faces) : EqOn f (a t) (convexHull ℝ (t.val : Set E)) := by
    intro x hx
    have hxK := convexHull_subset_space t.property hx
    dsimp only [f]
    rw [dif_pos hxK]
    exact hcompat _ t ⟨hface ⟨x, hxK⟩, hx⟩
  refine ⟨f, fun t ht => ⟨a ⟨t, ht⟩, hformula ⟨t, ht⟩⟩, ?_⟩
  intro x hx
  exact (hformula ⟨{x}, hx⟩ (by simp)).trans (ha ⟨{x}, hx⟩ (by simp))

end Geometry.SimplicialComplex
