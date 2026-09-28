import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ModelParameters
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFiniteAffineCover
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalSegments
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.TwoSegmentGermDegree
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph










set_option autoImplicit false
open Set Metric Geometry Topology Filter

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [DecidableEq E] in

theorem face_card_le_two_of_polygon_carrier
    (K : SimplicialComplex ℝ E) {n : ℕ} (P : Polygon E (n + 3))
    (hKP : K.space ⊆ P.boundary ℝ) {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ 2 := by
  classical
  have hcover : convexHull ℝ (s : Set E) ⊆
      ⋃ j : Fin (n + 3), (affineSpan ℝ (P.edgeVertices j : Set E) : Set E) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hKP (K.convexHull_subset_space hs hx))
    rw [P.edgeSet_eq_convexHull] at hj
    exact mem_iUnion.mpr ⟨j, convexHull_subset_affineSpan _ hj⟩
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    (K.nonempty_of_mem_faces hs).to_set.mono (subset_convexHull ℝ _)
  obtain ⟨j, hj⟩ := (convex_convexHull ℝ (s : Set E)).exists_subset_affineSubspace_of_subset_iUnion
    hne (fun j : Fin (n + 3) ↦ affineSpan ℝ (P.edgeVertices j : Set E)) hcover
  exact ((K.indep hs).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans hj)).trans
      ((Finset.card_insert_le _ _).trans (by simp))


theorem polygon_carrier_two_neighbors
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPK : P.boundary ℝ = K.space) :
    ∀ v, (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
  intro v
  obtain ⟨u, w, hu, hw, huw, _, hlocal⟩ := P.exists_local_segment_pair hP hPi
    (hPK.symm.subset (K.vertices_subset_space v.property))
  exact K.ncard_neighborSet_eq_two_of_local_segments hK
    (fun s hs ↦ K.face_card_le_two_of_polygon_carrier P hPK.symm.subset hs)
    v.property hu hw huw.subset (by simpa only [hPK] using hlocal)



theorem exists_exact_cyclic_polygon_of_polygon_carrier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconn : IsConnected K.space)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPK : P.boundary ℝ = K.space) :
    ∃ (m : ℕ) (Q : Polygon E (m + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ range Q = K.vertices ∧ Q.boundary ℝ = K.space ∧
      (∀ s : Finset E, s ∈ K.faces ↔ s.Nonempty ∧
        ∃ j : Fin (m + 3), s ⊆ {Q j, Q (finRotate (m + 3) j)}) ∧
      ∀ s : Finset E, (s ∈ K.faces ∧ s.card = 2) ↔
        ∃ j : Fin (m + 3), s = {Q j, Q (finRotate (m + 3) j)} := by
  classical
  have : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let G := K.vertexAbstractComplex.edgeGraph
  obtain ⟨m, e, he⟩ := G.exists_cyclic_labels_of_two_neighbors
    (K.connected_edgeGraph_of_isConnected hK hconn)
    (K.polygon_carrier_two_neighbors hK P hP hPi hPK)
  let Q : Polygon E (m + 3) := ⟨fun j ↦ (e j : E)⟩
  have hQi : Function.Injective Q := fun j k hjk ↦ e.injective (Subtype.ext hjk)
  have hface (j : Fin (m + 3)) : {Q j, Q (finRotate (m + 3) j)} ∈ K.faces := by
    have h := ((he (e j) (e (j + 1))).mpr ⟨j, Or.inl ⟨rfl, rfl⟩⟩).2
    change ({e j, e (j + 1)} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [Q, finRotate_apply, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using h
  have hdim (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 2 :=
    K.face_card_le_two_of_polygon_carrier P hPK.symm.subset hs
  have hfaces (s : Finset E) : s ∈ K.faces ↔ s.Nonempty ∧
      ∃ j : Fin (m + 3), s ⊆ {Q j, Q (finRotate (m + 3) j)} := by
    constructor
    · intro hs
      refine ⟨K.nonempty_of_mem_faces hs, ?_⟩
      have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
      have hle := hdim s hs
      by_cases hs1 : s.card = 1
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs1
        have hx : x ∈ K.vertices := hs
        obtain ⟨j, hj⟩ := e.surjective ⟨x, hx⟩
        refine ⟨j, Finset.singleton_subset_iff.mpr ?_⟩
        have hval : Q j = x := congrArg Subtype.val hj
        rw [← hval]
        exact Finset.mem_insert_self _ _
      · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
        have hx : x ∈ K.vertices := K.down_closed hs
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) (Finset.singleton_nonempty _)
        have hy : y ∈ K.vertices := K.down_closed hs
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (Finset.singleton_nonempty _)
        have hadj : G.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
          refine ⟨fun h ↦ hxy (congrArg Subtype.val h), ?_⟩
          change ({(⟨x, hx⟩ : K.vertices), ⟨y, hy⟩} : Finset K.vertices).map
            (Function.Embedding.subtype _) ∈ K.faces
          simpa only [Finset.map_insert, Finset.map_singleton,
            Function.Embedding.coe_subtype] using hs
        obtain ⟨j, hj⟩ := (he _ _).mp hadj
        refine ⟨j, ?_⟩
        rcases hj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
        · have h0 : Q j = x := congrArg Subtype.val hj0
          have h1 : Q (finRotate _ j) = y := by simpa only [finRotate_apply] using congrArg Subtype.val hj1
          rw [h0, h1]
        · have h0 : Q j = y := congrArg Subtype.val hj0
          have h1 : Q (finRotate _ j) = x := by simpa only [finRotate_apply] using congrArg Subtype.val hj1
          rw [h0, h1, Finset.pair_comm x y]
    · rintro ⟨hne, j, hj⟩
      exact K.down_closed (hface j) hj hne
  have hboundary : Q.boundary ℝ = K.space := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      apply K.convexHull_subset_space (hface j)
      simpa only [Polygon.edgeSet, affineSegment_eq_segment, Finset.coe_pair,
        convexHull_pair, finRotate_apply] using hj
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      obtain ⟨j, hj⟩ := ((hfaces s).mp hs).2
      refine mem_iUnion.mpr ⟨j, ?_⟩
      rw [Q.edgeSet_eq_convexHull]
      simpa only [Polygon.edgeVertices, finRotate_apply, Finset.coe_pair] using
        convexHull_mono hj hxs
  have hQs : Q.HasSimplicialEdges := by
    intro j k
    simpa only [Q.edgeSet_eq_convexHull, Polygon.edgeVertices, finRotate_apply, Finset.coe_pair] using
      K.inter_subset_convexHull (hface j) (hface k)
  refine ⟨m, Q, hQi, hQs, ?_, hboundary, hfaces, ?_⟩
  · ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (e j).property
    · intro hx
      obtain ⟨j, hj⟩ := e.surjective ⟨x, hx⟩
      exact ⟨j, congrArg Subtype.val hj⟩
  · intro s
    constructor
    · rintro ⟨hs, hcard⟩
      obtain ⟨j, hj⟩ := ((hfaces s).mp hs).2
      exact ⟨j, Finset.eq_of_subset_of_card_le hj (by
        rw [hcard]
        exact (Finset.card_insert_le _ _).trans (by simp))⟩
    · rintro ⟨j, rfl⟩
      refine ⟨hface j, Finset.card_pair ?_⟩
      apply hQi.ne
      intro h
      have h' : (1 : Fin (m + 3)) = 0 := add_left_cancel
        (show j + 1 = j + 0 by simpa only [finRotate_apply, add_zero] using h.symm)
      have hv := congrArg Fin.val h'
      norm_num at hv

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)



theorem OrdinaryIntervalMarkedModel.exists_exact_model_circle_order
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : OrdinaryIntervalMarkedModel old i) {n : ℕ} (P : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hPs : P.boundary ℝ = old.pieces i) :
    ∃ (m : ℕ) (Q : Polygon (D.sample → ℝ × V3) (m + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ range Q = (D.marks (.inr 2)).vertices ∧
      Q.boundary ℝ = (D.marks (.inr 2)).space ∧
      (∀ s : Finset (D.sample → ℝ × V3), s ∈ (D.marks (.inr 2)).faces ↔ s.Nonempty ∧
        ∃ j : Fin (m + 3), s ⊆ {Q j, Q (finRotate (m + 3) j)}) ∧
      ∀ s : Finset (D.sample → ℝ × V3),
        (s ∈ (D.marks (.inr 2)).faces ∧ s.card = 2) ↔
          ∃ j : Fin (m + 3), s = {Q j, Q (finRotate (m + 3) j)} := by
  classical
  obtain ⟨k, Q, hQi, hQ, hQs⟩ := D.exists_model_circle_polygon P hP hPi hPs
  obtain ⟨hPL, _, himage⟩ := D.selected_graph_finitePL
  have hconn : IsConnected (D.marks (.inr 2)).space := by
    rw [← himage]
    exact (old.connected i).image (D.graph ∘ f) hPL.continuousOn
  exact (D.marks (.inr 2)).exists_exact_cyclic_polygon_of_polygon_carrier
    (D.marks_full (.inr 2)).2.1 hconn Q hQ hQi hQs

end PoincareConjecture.M76.Dehn
