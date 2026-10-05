import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedFaceCenterLink
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedMaximalFaceStars
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedVertexLinkConnected
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedSurfacePurity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedSurfaceIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.PositiveFaceCenterAtPoint
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexFrontierConnected
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FiniteCarrierFaceInteriors

/-!
# The actual derived surface at a prescribed carrier point

Positive centers give connected links in all three original
face dimensions. The same derived surface can therefore be
centered at any prescribed original carrier point, retaining
purity, paired cofaces and the entire original carrier.
See Hudson 1969, pp. 8--9, Cairns 1940, pp. 799, 801--805,
and M76 derivation 286be.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Every positive original face center has connected actual
derived link when the original pure triangular complex has
connected vertex links. See Cairns pp. 801--802, Hudson
pp. 8--9 and M76 derivation 286be. -/
theorem connected_derived_faceCenter_link_of_pure_triangles
    (K : SimplicialComplex ℝ E) [Fintype K.faces] (c : K.faces → E)
    (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
      (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space) (s : K.faces) :
    ((K.derivedSubdivision c hc).link (c s)).vertexAbstractComplex.edgeGraph.Connected := by
  classical
  have hbound (t : Finset E) (ht : t ∈ K.faces) : t.card ≤ 3 := by
    obtain ⟨u, _, huc, htu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hsne := K.nonempty_of_mem_faces s.property
  have hcases : s.val.card = 1 ∨ s.val.card = 2 ∨ s.val.card = 3 := by
    have hpos := hsne.card_pos
    have hle := hbound s.val s.property
    omega
  rcases hcases with hsingle | hedge | htriangle
  · obtain ⟨v, hsv⟩ := Finset.card_eq_one.mp hsingle
    have hvK : {v} ∈ K.faces := hsv ▸ s.property
    have hcs : c s = v := by
      have he : s = ⟨{v}, hvK⟩ := Subtype.ext hsv
      rw [he]
      exact K.positiveFaceCenter_singleton c hc hvK
    rw [hcs]
    exact ((K.derivedSubdivision c hc).link v).connected_edgeGraph_of_isConnected
      (finite_link_faces (K.derivedSubdivision_finite c hc) v)
      (K.isConnected_derived_original_vertex_link c hc hvK (hlinks v hvK))
  · obtain ⟨v, hv⟩ := hsne
    let r : K.faces := ⟨{v}, K.down_closed s.property
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)⟩
    obtain ⟨t, ht, htc, hst⟩ := hpure s.val s.property
    let u : K.faces := ⟨t, ht⟩
    have hrs : r < s := by
      apply lt_iff_le_not_ge.mpr
      refine ⟨Finset.singleton_subset_iff.mpr hv, ?_⟩
      intro h
      have hcard := Finset.card_le_card h
      change s.val.card ≤ ({v} : Finset E).card at hcard
      simp only [Finset.card_singleton] at hcard
      omega
    have hsu : s < u := by
      apply lt_iff_le_not_ge.mpr
      refine ⟨hst, ?_⟩
      intro h
      have hcard : t.card ≤ s.val.card := Finset.card_le_card h
      omega
    exact K.connected_derived_faceCenter_link_of_strict_faces c hc r s u hrs hsu
  · have hmax (t : K.faces) (hst : s ≤ t) : t = s :=
      Subtype.ext (Finset.eq_of_subset_of_card_le hst
        (by simpa only [htriangle] using hbound t.val t.property)).symm
    apply ((K.derivedSubdivision c hc).link (c s)).connected_edgeGraph_of_isConnected
      (finite_link_faces (K.derivedSubdivision_finite c hc) (c s))
    rw [K.derived_link_faceCenter_space_of_maximal c hc s hmax]
    exact (K.indep s.property).isConnected_intrinsicFrontier_convexHull_finset htriangle.ge

/-- The actual derived surface can be centered at any prescribed
original face-interior point, with all surface incidences and
its connected link retained. In a triangle its full star and
link are the original hull and intrinsic frontier. See Hudson
pp. 8--9 and M76 derivation 286be. -/
theorem exists_centered_derived_surface_at_face_point
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (s : K.faces) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E))) :
    ∃ M : SimplicialComplex ℝ E, M.faces.Finite ∧ M.space = K.space ∧ p ∈ M.vertices ∧
      (∀ u ∈ M.faces, ∃ t ∈ M.faces, t.card = 3 ∧ u ⊆ t) ∧
      (∀ u ∈ M.faces, u.card = 2 →
        {t : Finset E | t ∈ M.faces ∧ t.card = 3 ∧ u ⊆ t}.ncard = 2) ∧
      (M.link p).vertexAbstractComplex.edgeGraph.Connected ∧
      (s.val.card = 3 →
        (M.closedStar p).space = convexHull ℝ (s.val : Set E) ∧
        (M.link p).space = intrinsicFrontier ℝ (convexHull ℝ (s.val : Set E))) := by
  classical
  let : Fintype K.faces := hK.fintype
  obtain ⟨c, hc, hcs⟩ := K.exists_positive_face_centers_at_point s hp
  have hbound (t : Finset E) (ht : t ∈ K.faces) : t.card ≤ 3 := by
    obtain ⟨u, _, huc, htu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hpM : p ∈ (K.derivedSubdivision c hc).vertices := by
    rw [← hcs, K.derivedSubdivision_vertices_eq_range c hc]
    exact mem_range_self s
  have hconn : ((K.derivedSubdivision c hc).link p).vertexAbstractComplex.edgeGraph.Connected := by
    rw [← hcs]
    exact K.connected_derived_faceCenter_link_of_pure_triangles c hc hpure hlinks s
  refine ⟨K.derivedSubdivision c hc, K.derivedSubdivision_finite c hc,
    K.derivedSubdivision_space c hc, hpM, K.derivedSubdivision_pure_triangles c hc hpure,
    K.derivedSubdivision_two_triangle_cofaces c hc hbound hcofaces, hconn, ?_⟩
  intro htriangle
  have hmax (t : K.faces) (hst : s ≤ t) : t = s :=
    Subtype.ext (Finset.eq_of_subset_of_card_le hst
      (by simpa only [htriangle] using hbound t.val t.property)).symm
  rw [← hcs]
  exact ⟨K.derived_closedStar_faceCenter_space_of_maximal c hc s hmax,
    K.derived_link_faceCenter_space_of_maximal c hc s hmax⟩

/-- Every prescribed point of the complete original surface
is an actual vertex with connected link in a finite auxiliary
surface with the same carrier, purity and paired cofaces.
See Cairns pp. 799, 801--805 and M76 derivation 286be. -/
theorem exists_centered_derived_surface_at_carrier_point
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.space) :
    ∃ M : SimplicialComplex ℝ E, M.faces.Finite ∧ M.space = K.space ∧ p ∈ M.vertices ∧
      (∀ u ∈ M.faces, ∃ t ∈ M.faces, t.card = 3 ∧ u ⊆ t) ∧
      (∀ u ∈ M.faces, u.card = 2 →
        {t : Finset E | t ∈ M.faces ∧ t.card = 3 ∧ u ⊆ t}.ncard = 2) ∧
      (M.link p).vertexAbstractComplex.edgeGraph.Connected := by
  obtain ⟨s, hs, hps⟩ := K.exists_face_intrinsicInterior_of_finite hK hp
  obtain ⟨M, hM, hMK, hpM, hpureM, hcofacesM, hlinkM, _⟩ :=
    K.exists_centered_derived_surface_at_face_point hK hpure hcofaces hlinks ⟨s, hs⟩ hps
  exact ⟨M, hM, hMK, hpM, hpureM, hcofacesM, hlinkM⟩

end Geometry.SimplicialComplex
