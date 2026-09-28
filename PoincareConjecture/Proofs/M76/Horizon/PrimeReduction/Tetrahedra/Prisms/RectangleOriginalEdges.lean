import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt.OriginalFaceRectangles

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}

def edgeVertices (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) : Finset E :=
  {D.edge k b 0,D.edge k b 1}

theorem side_subset_edge_hull (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    D.side k b ⊆ convexHull ℝ (D.edgeVertices k b : Set E) := by
  intro x hx
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨_,_,_,_,hlo,hhi,_⟩ := D.edgeData k b
  have h := (affine_unit_interval_image (D.edge k b)).subset
    (mem_image_of_mem (D.edge k b) ⟨hlo.1.le.trans hu.1,hu.2.trans hhi.2.le⟩)
  simpa only [edgeVertices,Finset.coe_insert,Finset.coe_singleton] using h

theorem side_disjoint_original_vertices
    (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    Disjoint (D.side k b) K.vertices := by
  refine disjoint_left.mpr ?_
  intro x hx hxK
  have hxend := (K.vertex_mem_convexHull_iff hxK (D.edgeData k b).2.1).mp
    (D.side_subset_edge_hull k b hx)
  obtain ⟨u,hu,huX⟩ := hx
  obtain ⟨hei,_,_,_,hlo,hhi,_⟩ := D.edgeData k b
  have hu0 : 0 < u := hlo.1.trans_le hu.1
  have hu1 : u < 1 := hu.2.trans_lt hhi.2
  simp only [edgeVertices,Finset.mem_insert,Finset.mem_singleton] at hxend
  rcases hxend with hx0 | hx1
  · exact hu0.ne' (hei (huX.trans hx0))
  · exact hu1.ne (hei (huX.trans hx1))

theorem edgeVertices_false_ne_true (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    D.edgeVertices k false ≠ D.edgeVertices k true := by
  intro heq
  apply D.arcNonreturning (D.cap k false) (D.edgeVertices k false)
    (D.edgeData k false).2.2.1 (D.edgeData k false).2.2.2.1
  intro x hx
  have hxcap := (D.arcRim (D.cap k false)).subset hx
  have hxM := (D.regionBall k).1 (Or.inl (Or.inl hxcap.1))
  rcases (D.boundaryContact k).subset ⟨hxM,hxcap.2⟩ with hl | hr
  · exact D.side_subset_edge_hull k false hl
  · rw [heq]
    exact D.side_subset_edge_hull k true hr

theorem edgeVertices_injective (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    Function.Injective (D.edgeVertices k) := by
  intro b c he
  cases b <;> cases c <;> try rfl
  · exact False.elim (D.edgeVertices_false_ne_true k he)
  · exact False.elim (D.edgeVertices_false_ne_true k he.symm)

theorem exists_unique_side_on_original_edge
    (D : OriginalFaceRectangles K g S s) (k : D.Region)
    {a : Finset E} (ha : a ∈ K.faces) (ha2 : a.card = 2)
    {x : E} (hxM : x ∈ D.carrier k)
    (hxF : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hxa : x ∈ convexHull ℝ (a : Set E)) :
    ∃! b : Bool, x ∈ D.side k b ∧ D.edgeVertices k b = a := by
  have hex : ∃ b : Bool, x ∈ D.side k b := by
    rcases (D.boundaryContact k).subset ⟨hxM,hxF⟩ with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ := hex
  have hne : x ∉ (D.edgeVertices k b : Set E) := fun hv =>
    disjoint_left.mp (D.side_disjoint_original_vertices k b) hb
      (K.face_subset_vertices (D.edgeData k b).2.1 hv)
  have heq := original_edges_eq_of_nonvertex_contact K (D.edgeData k b).2.1 ha
    (D.edgeData k b).2.2.2.1 ha2 (D.side_subset_edge_hull k b hb) hxa hne
  refine ⟨b,⟨hb,heq⟩,?_⟩
  intro c hc
  exact D.edgeVertices_injective k (hc.2.trans heq.symm)

end PoincareConjecture.M76.PrismBelt.OriginalFaceRectangles
