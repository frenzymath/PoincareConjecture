import PoincareLib.Topology.Manifold.Smoothing.Dehn.Topology.Mathlib.OriginalEdgeComponentConnected
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.ClosedRegionPatchIncidence

/-!
# The whole connected rim image lies in one complete original component

All original component carriers form a disjoint cover. Their actual
finite face collections make them closed. Thus a connected original
rim image lies in one entire component, without a connectivity
assumption on the full boundary or its open mark.
See Stallings p. 11 and Dehn derivation 024, section 4.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

/-- The actual whole component carriers cover exactly the original
complex carrier. Every original simplex is retained in the component
of any one of its vertices. See Dehn 024, section 4. -/
theorem iUnion_edgeComponentComplex_space :
    (⋃ C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (K.edgeComponentComplex C).space) = K.space := by
  ext x
  constructor
  · rintro hx
    obtain ⟨C, hC⟩ := mem_iUnion.mp hx
    exact space_subset_of_le (K.edgeComponentComplex_le C) hC
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hs
    have hv : v ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    let C := K.vertexAbstractComplex.edgeGraph.connectedComponentMk ⟨v, hv⟩
    have hvC : v ∈ (K.edgeComponentComplex C).vertices :=
      (K.edgeComponentComplex_vertex_iff C ⟨v, hv⟩).mpr rfl
    have hsC : s ∈ (K.edgeComponentComplex C).faces :=
      K.edgeComponentComplex_coface C hvC hs (Finset.singleton_subset_iff.mpr hvs)
    exact mem_iUnion.mpr ⟨C, (K.edgeComponentComplex C).convexHull_subset_space hsC hxs⟩

/-- Distinct complete original components have disjoint carriers.
A point in two simplex hulls would give a shared original vertex.
See Dehn 024, section 4. -/
theorem pairwise_disjoint_edgeComponentComplex_space :
    Pairwise (fun C D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (K.edgeComponentComplex C).space (K.edgeComponentComplex D).space) := by
  intro C D hCD
  apply disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxC
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxD
  have hx := K.inter_subset_convexHull hs.1 ht.1 ⟨hxs, hxt⟩
  obtain ⟨v, hvs, hvt⟩ := convexHull_nonempty_iff.mp ⟨x, hx⟩
  obtain ⟨a, haC, hav⟩ := hs.2 v hvs
  obtain ⟨b, hbD, hbv⟩ := ht.2 v hvt
  have hab : a = b := Subtype.ext (hav.trans hbv.symm)
  exact disjoint_left.mp
    (K.vertexAbstractComplex.edgeGraph.pairwise_disjoint_supp_connectedComponent hCD)
    haC (hab.symm ▸ hbD)

/-- The entire connected original rim image belongs to one complete
boundary component. Finiteness and closedness are derived from the
original face collection. See Stallings p. 11 and Dehn024, section 4. -/
theorem exists_edgeComponentComplex_of_isConnected
    (hK : K.faces.Finite) {s : Set E} (hs : IsConnected s) (hsK : s ⊆ K.space) :
    ∃ C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      s ⊆ (K.edgeComponentComplex C).space := by
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  have hclosed (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      IsClosed (K.edgeComponentComplex C).space :=
    ((K.edgeComponentComplex C).isCompact_space_of_finite
      (hK.subset (fun _ ht => ht.1))).isClosed
  have hcover : s ⊆ ⋃ C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (K.edgeComponentComplex C).space := by
    rw [K.iUnion_edgeComponentComplex_space]
    exact hsK
  have hpair : Pairwise (fun C D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      (K.edgeComponentComplex C).space ∩ (K.edgeComponentComplex D).space ⊆ (∅ : Set E)) :=
    fun _ _ h => (disjoint_iff_inter_eq_empty.mp
      (K.pairwise_disjoint_edgeComponentComplex_space h)).subset
  obtain ⟨C, hC⟩ := hs.exists_closure_subset_of_finite_closed_cover
    (fun C => (K.edgeComponentComplex C).space) hclosed hcover hpair (disjoint_empty s)
  exact ⟨C, subset_closure.trans hC⟩

end Geometry.SimplicialComplex
