import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceCountInclusionExclusion









set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)



theorem iUnion_edgeComponentComplex_faces :
    (⋃ C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (K.edgeComponentComplex C).faces) = K.faces := by
  ext s
  constructor
  · intro hs
    obtain ⟨C, hsC⟩ := mem_iUnion.mp hs
    exact K.edgeComponentComplex_le C hsC
  · intro hs
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hs
    have hv : v ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    let C := K.vertexAbstractComplex.edgeGraph.connectedComponentMk ⟨v, hv⟩
    have hvC := (K.edgeComponentComplex_vertex_iff C ⟨v, hv⟩).mpr rfl
    exact mem_iUnion.mpr ⟨C, K.edgeComponentComplex_coface C hvC hs
      (Finset.singleton_subset_iff.mpr hvs)⟩


theorem pairwise_disjoint_edgeComponentComplex_faces :
    Pairwise fun C D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (K.edgeComponentComplex C).faces (K.edgeComponentComplex D).faces := by
  intro C D hCD
  apply disjoint_left.mpr
  intro s hsC hsD
  obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hsC.1
  obtain ⟨p, hp, hpv⟩ := hsC.2 v hvs
  obtain ⟨q, hq, hqv⟩ := hsD.2 v hvs
  have hpq : p = q := Subtype.ext (hpv.trans hqv.symm)
  exact disjoint_left.mp
    (K.vertexAbstractComplex.edgeGraph.pairwise_disjoint_supp_connectedComponent hCD)
    hp (hpq.symm ▸ hq)



def selectedEdgeComponents
    (A : Finset K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    SimplicialComplex ℝ E :=
  K.vertexSubcomplex (⋃ C ∈ A, Subtype.val '' C.supp)

theorem selectedEdgeComponents_le
    (A : Finset K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    K.selectedEdgeComponents A ≤ K := K.vertexSubcomplex_le _



theorem selectedEdgeComponents_faces
    (A : Finset K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    (K.selectedEdgeComponents A).faces = ⋃ C ∈ A, (K.edgeComponentComplex C).faces := by
  ext s
  constructor
  · intro hs
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hs.1
    obtain ⟨C, hC⟩ := mem_iUnion.mp (hs.2 v hvs)
    obtain ⟨hCA, p, hpC, hpv⟩ := mem_iUnion.mp hC
    have hpface : p.val ∈ s := hpv.symm ▸ hvs
    have hpvertex := (K.edgeComponentComplex_vertex_iff C p).mpr hpC
    exact mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨hCA,
      K.edgeComponentComplex_coface C hpvertex hs.1 (Finset.singleton_subset_iff.mpr hpface)⟩⟩
  · intro hs
    obtain ⟨C, hC⟩ := mem_iUnion.mp hs
    obtain ⟨hCA, hsC⟩ := mem_iUnion.mp hC
    refine ⟨hsC.1, ?_⟩
    intro v hv
    exact mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨hCA, hsC.2 v hv⟩⟩



theorem selectedEdgeComponents_space
    (A : Finset K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    (K.selectedEdgeComponents A).space =
      ⋃ C ∈ A, (K.edgeComponentComplex C).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    rw [K.selectedEdgeComponents_faces] at hs
    obtain ⟨C, hC⟩ := mem_iUnion.mp hs
    obtain ⟨hCA, hsC⟩ := mem_iUnion.mp hC
    exact mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨hCA,
      (K.edgeComponentComplex C).convexHull_subset_space hsC hxs⟩⟩
  · intro hx
    obtain ⟨C, hC⟩ := mem_iUnion.mp hx
    obtain ⟨hCA, hxC⟩ := mem_iUnion.mp hC
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxC
    apply mem_space_iff.mpr
    refine ⟨s, ?_, hxs⟩
    rw [K.selectedEdgeComponents_faces]
    exact mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨hCA, hs⟩⟩



theorem selectedEdgeComponents_card_faceOfCard (hK : K.faces.Finite)
    (A : Finset K.vertexAbstractComplex.edgeGraph.ConnectedComponent) (n : ℕ) :
    Nat.card ((K.selectedEdgeComponents A).FaceOfCard n) =
      ∑ C ∈ A, Nat.card ((K.edgeComponentComplex C).FaceOfCard n) := by
  classical
  let hA := hK.subset (K.selectedEdgeComponents_le A)
  let hC := fun C => hK.subset (K.edgeComponentComplex_le C)
  let faces := fun C => (hC C).toFinset.filter (fun s => s.card = n)
  have hcard (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
      Nat.card (L.FaceOfCard n) = (hL.toFinset.filter (fun s => s.card = n)).card :=
    Nat.subtype_card _ (by intro s; simp)
  have hpartition : hA.toFinset.filter (fun s => s.card = n) = A.biUnion faces := by
    ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, K.selectedEdgeComponents_faces,
      mem_iUnion, Finset.mem_biUnion, faces]
    aesop
  have hdisjoint : Set.PairwiseDisjoint (A : Set _) faces := by
    intro C _ D _ hCD
    apply Finset.disjoint_left.mpr
    intro s hsC hsD
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_faces hCD)
      ((hC C).mem_toFinset.mp (Finset.mem_filter.mp hsC).1)
      ((hC D).mem_toFinset.mp (Finset.mem_filter.mp hsD).1)
  rw [hcard _ hA, hpartition, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro C _
  exact (hcard _ (hC C)).symm



theorem selectedEdgeComponents_surfaceEulerCount (hK : K.faces.Finite)
    (A : Finset K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    (K.selectedEdgeComponents A).surfaceEulerCount =
      ∑ C ∈ A, (K.edgeComponentComplex C).surfaceEulerCount := by
  simp only [surfaceEulerCount, K.selectedEdgeComponents_card_faceOfCard hK A,
    Nat.cast_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]



theorem selectedEdgeComponents_surfaceEulerCount_indexed (hK : K.faces.Finite)
    {ι : Type*} [Fintype ι]
    (pick : ι ↪ K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    (K.selectedEdgeComponents (Finset.univ.map pick)).surfaceEulerCount =
      ∑ i, (K.edgeComponentComplex (pick i)).surfaceEulerCount := by
  rw [K.selectedEdgeComponents_surfaceEulerCount hK, Finset.sum_map]


theorem selectedEdgeComponents_univ
    [Fintype K.vertexAbstractComplex.edgeGraph.ConnectedComponent] :
    K.selectedEdgeComponents Finset.univ = K := by
  apply SimplicialComplex.ext
  rw [K.selectedEdgeComponents_faces]
  simpa only [Finset.mem_univ, iUnion_true] using K.iUnion_edgeComponentComplex_faces




theorem surfaceEulerCount_eq_sum_edgeComponents (hK : K.faces.Finite) :
    letI : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
    letI : Fintype K.vertexAbstractComplex.edgeGraph.ConnectedComponent := Fintype.ofFinite _
    K.surfaceEulerCount = ∑ C, (K.edgeComponentComplex C).surfaceEulerCount := by
  letI : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  letI : Fintype K.vertexAbstractComplex.edgeGraph.ConnectedComponent := Fintype.ofFinite _
  simpa only [K.selectedEdgeComponents_univ] using
    K.selectedEdgeComponents_surfaceEulerCount hK Finset.univ

end Geometry.SimplicialComplex
