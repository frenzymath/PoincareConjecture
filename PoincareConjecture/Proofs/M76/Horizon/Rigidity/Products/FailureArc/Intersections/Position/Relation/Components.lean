import PoincareConjecture.Proofs.M76.Mathlib.GeometricPathIntervals
import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons
import PoincareConjecture.Proofs.M76.Mathlib.ComplexCycleLabels
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn

open Classical in
theorem exists_intrinsic_ordinary_graph_components
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : SimplicialComplex ℝ E) (Q : Set E)
    (hG : G.faces.Finite) (hcard : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if (v : E) ∈ Q then 1 else 2)
    (hrim : G.space ∩ Q = Subtype.val '' {v : G.vertices |
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1}) :
    ∃ pieces : G.vertexAbstractComplex.edgeGraph.ConnectedComponent → Set E,
      Finite G.vertexAbstractComplex.edgeGraph.ConnectedComponent ∧
      (∀ A, pieces A = A.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) ∧
      G.space = ⋃ A, pieces A ∧
      Pairwise (fun A B => Disjoint (pieces A) (pieces B)) ∧
      (∀ A, IsCompact (pieces A) ∧ IsConnected (pieces A) ∧
        IsClopen ((Subtype.val : G.space → E) ⁻¹' pieces A)) ∧
      (∀ A, IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) ∨
        ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
          P.HasSimplicialEdges ∧ P.boundary ℝ = pieces A ∧ Disjoint (pieces A) Q) ∧
      (∃ c : ConnectedComponents G.space ≃ G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        ∀ (x : G.space) A, c (ConnectedComponents.mk x) = A ↔ (x : E) ∈ pieces A) ∧
      (ConnectedComponents.mk '' ((Subtype.val : G.space → E) ⁻¹' Q)).ncard =
        {A | (pieces A ∩ Q).Nonempty}.ncard ∧
      (ConnectedComponents.mk '' ((Subtype.val : G.space → E) ⁻¹' Q))ᶜ.ncard =
        {A | Disjoint (pieces A) Q}.ncard := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let Γ := G.vertexAbstractComplex.edgeGraph
  let pieces := fun A : Γ.ConnectedComponent =>
    A.toSimpleGraph.segmentCarrier (fun v => (v.val : E))
  have hedge {v w : G.vertices} (hvw : Γ.Adj v w) :
      ({(v : E), (w : E)} : Finset E) ∈ G.faces := by
    have h := hvw.2
    change ({v, w} : Finset G.vertices).map (Function.Embedding.subtype _) ∈ G.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      using h
  have hinter {v w a b : G.vertices} (hvw : Γ.Adj v w) (hab : Γ.Adj a b) :
      segment ℝ (v : E) (w : E) ∩ segment ℝ (a : E) (b : E) ⊆
        convexHull ℝ (({(v : E), (w : E)} : Set E) ∩ {(a : E), (b : E)}) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      G.inter_subset_convexHull (hedge hvw) (hedge hab)
  have hpositive (v : G.vertices) : 0 < (Γ.neighborSet v).ncard := by
    change 0 < (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard
    rw [hdegree]
    split_ifs <;> norm_num
  have hdegree2 (v : G.vertices) : (Γ.neighborSet v).ncard ≤ 2 := by
    change (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2
    rw [hdegree]
    split_ifs <;> norm_num
  have hvertex (A : Γ.ConnectedComponent) (v : A) : (v.val : E) ∈ pieces A := by
    obtain ⟨w, hvw⟩ := (Set.ncard_pos (Set.toFinite (Γ.neighborSet v.val))).mp
      (hpositive v.val)
    have hw : w ∈ A.supp := A.mem_supp_of_adj_mem_supp v.property hvw
    exact ⟨v, ⟨w, hw⟩, hvw, left_mem_segment ℝ _ _⟩
  have hcarrier : Γ.segmentCarrier (Subtype.val : G.vertices → E) = G.space := by
    apply subset_antisymm
    · rintro x ⟨v, w, hvw, hx⟩
      exact G.convexHull_subset_space (hedge hvw)
        (by simpa only [Finset.coe_pair, convexHull_pair] using hx)
    · intro x hx
      obtain ⟨face, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
      have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hf)
      rcases (show face.card = 1 ∨ face.card = 2 by have := hcard face hf; omega) with h1 | h2
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
        have hxv : x = v := by
          simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hxf
        subst x
        obtain ⟨w, hvw⟩ := (Set.ncard_pos (Set.toFinite (Γ.neighborSet ⟨v, hf⟩))).mp
          (hpositive ⟨v, hf⟩)
        exact ⟨⟨v, hf⟩, w, hvw, left_mem_segment ℝ _ _⟩
      · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp h2
        have hv := G.face_subset_vertices hf (Finset.mem_insert_self _ _)
        have hw := G.face_subset_vertices hf (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _))
        have hadj : Γ.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
          refine ⟨fun h => hvw (congrArg Subtype.val h), ?_⟩
          change ({(⟨v, hv⟩ : G.vertices), ⟨w, hw⟩} : Finset G.vertices).map
            (Function.Embedding.subtype _) ∈ G.faces
          simpa only [Finset.map_insert, Finset.map_singleton,
            Function.Embedding.coe_subtype] using hf
        exact ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj,
          by simpa only [Finset.coe_pair, convexHull_pair] using hxf⟩
  have hcover : G.space = ⋃ A, pieces A :=
    hcarrier.symm.trans (Γ.segmentCarrier_eq_iUnion_components _)
  have hsub (A : Γ.ConnectedComponent) : pieces A ⊆ G.space :=
    fun _ hx => hcover.symm.subset (mem_iUnion.mpr ⟨A, hx⟩)
  have hdisj : Pairwise (fun A B => Disjoint (pieces A) (pieces B)) :=
    Γ.pairwise_disjoint_component_segmentCarrier _ Subtype.val_injective
      (fun {_ _ _ _} h h' => hinter h h')
  have hsame {A B : Γ.ConnectedComponent} {x : E}
      (hx : x ∈ pieces A) (hy : x ∈ pieces B) : A = B := by
    by_contra h
    exact disjoint_left.mp (hdisj h) hx hy
  have hboundary (A : Γ.ConnectedComponent) : pieces A ∩ Q =
      (fun v : A => (v.val : E)) ''
        {v | (A.toSimpleGraph.neighborSet v).ncard = 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hvx⟩ := hrim.subset ⟨hsub A hx.1, hx.2⟩
      let B := Γ.connectedComponentMk v
      have hvB : v ∈ B.supp := rfl
      have hBA : B = A := hsame (hvertex B ⟨v, hvB⟩) (hvx.symm ▸ hx.1)
      have hvA : v ∈ A.supp := hBA ▸ hvB
      exact ⟨⟨v, hvA⟩, (A.ncard_neighborSet Γ ⟨v, hvA⟩).trans hv, hvx⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨hvertex A v, ?_⟩
      exact (hrim.symm.subset ⟨v.val,
        (A.ncard_neighborSet Γ v).symm.trans hv, rfl⟩).2
  have hmodels (A : Γ.ConnectedComponent) :
      IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) ∨
        ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
          P.HasSimplicialEdges ∧ P.boundary ℝ = pieces A ∧ Disjoint (pieces A) Q := by
    by_cases hleaf : ∃ v : A, (A.toSimpleGraph.neighborSet v).ncard = 1
    · left
      rw [hboundary]
      exact A.toSimpleGraph.isFinitePLBallPair_segmentCarrier_of_leaf
        (fun v => (v.val : E)) A.connected_toSimpleGraph
        (fun v => (A.ncard_neighborSet Γ v).le.trans (hdegree2 v.val)) hleaf
        (Subtype.val_injective.comp Subtype.val_injective)
        (fun {_ _ _ _} h h' => hinter h h')
    · have htwo (v : A) : (A.toSimpleGraph.neighborSet v).ncard = 2 := by
        have hpv := hpositive v.val
        have hb := hdegree2 v.val
        have heq := A.ncard_neighborSet Γ v
        have hn : (A.toSimpleGraph.neighborSet v).ncard ≠ 1 :=
          fun h => hleaf ⟨v, h⟩
        omega
      obtain ⟨n, P, hPi, hP, hPs⟩ := A.toSimpleGraph.exists_polygon_of_two_neighbors
        (fun v => (v.val : E)) A.connected_toSimpleGraph htwo
        (Subtype.val_injective.comp Subtype.val_injective)
        (fun {_ _ _ _} h h' => hinter h h')
      refine Or.inr ⟨n, P, hPi, hP, hPs, disjoint_iff_inter_eq_empty.mpr ?_⟩
      rw [hboundary]
      apply eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨v, hv, _⟩
      exact hleaf ⟨v, hv⟩
  have htop (A : Γ.ConnectedComponent) : IsCompact (pieces A) ∧ IsConnected (pieces A) := by
    rcases hmodels A with hball | ⟨n, P, hPi, hP, hPs, _⟩
    · exact ⟨hball.isCompact, hball.isConnected⟩
    · obtain ⟨eP⟩ := P.nonempty_boundary_homeomorph_circle hP hPi
      have hc : IsConnected (P.boundary ℝ) := isConnected_iff_connectedSpace.mpr
        (eP.connectedSpace_iff.mpr inferInstance)
      exact ⟨hPs ▸ P.isCompact_boundary, hPs ▸ hc⟩
  have hclopen (A : Γ.ConnectedComponent) :
      IsClopen ((Subtype.val : G.space → E) ⁻¹' pieces A) := by
    have hc : IsClosed ((Subtype.val : G.space → E) ⁻¹' pieces A) :=
      (htop A).1.isClosed.preimage continuous_subtype_val
    have hcompl : ((Subtype.val : G.space → E) ⁻¹' pieces A)ᶜ =
        ⋃ B : {B : Γ.ConnectedComponent // B ≠ A},
          (Subtype.val : G.space → E) ⁻¹' pieces B.val := by
      ext x
      constructor
      · intro hx
        obtain ⟨B, hxB⟩ := mem_iUnion.mp (hcover.subset x.property)
        exact mem_iUnion.mpr ⟨⟨B, fun h => hx (h ▸ hxB)⟩, hxB⟩
      · rintro hx hxA
        obtain ⟨B, hxB⟩ := mem_iUnion.mp hx
        exact B.property (hsame hxB hxA)
    refine ⟨hc, isClosed_compl_iff.mp ?_⟩
    rw [hcompl]
    exact isClosed_iUnion_of_finite fun B =>
      (htop B.val).1.isClosed.preimage continuous_subtype_val
  let U (A : Γ.ConnectedComponent) : Set G.space :=
    (Subtype.val : G.space → E) ⁻¹' pieces A
  have hucover : ⋃ A, U A = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ A, (x : E) ∈ pieces A
    exact mem_iUnion.mp (hcover.subset x.property)
  have huconn (A : Γ.ConnectedComponent) : IsConnected (U A) := by
    let : ConnectedSpace (pieces A) := isConnected_iff_connectedSpace.mp (htop A).2
    let j : pieces A → G.space := fun x => ⟨x, hsub A x.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have hr : range j = U A := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    exact hr ▸ isConnected_range hj
  obtain ⟨c, hc⟩ := exists_connected_components_equiv_of_finite_closed_partition U
    (fun A => (hclopen A).1) (fun _ _ h => (hdisj h).preimage _) hucover huconn
  have hcounts := connected_components_mark_counts_of_ambient_partition pieces
    (fun A => (htop A).1.isClosed) hdisj hcover.symm (fun A => (htop A).2) Q
  exact ⟨pieces, inferInstance, fun _ => rfl, hcover, hdisj,
    fun A => ⟨(htop A).1, (htop A).2, hclopen A⟩, hmodels, ⟨c, hc⟩, hcounts⟩

end PoincareConjecture.M76.Dehn
