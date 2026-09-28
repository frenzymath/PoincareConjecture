import PoincareConjecture.Proofs.M76.PrimeReduction.PureEdgeInterval
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem isFinitePLBallPair_boundary_edge_link_of_local_incidence
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    {s : Finset E}
    (hfacets : ∀ t ∈ K.faces, s ⊆ t → t.card = 3 →
      (t ∈ L.faces → (K.faceLink t).vertices.ncard = 1) ∧
      (t ∉ L.faces → (K.faceLink t).vertices.ncard = 2))
    (_hs : s ∈ L.faces) (hscard : s.card = 2)
    (hends : (L.faceLink s).vertices.ncard = 2)
    (hconn : IsConnected (K.faceLink s).space) :
    IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space := by
  classical
  let J := K.faceLink s
  have hJ : J.faces.Finite := finite_faceLink_faces hK s
  have hlinkle : L.faceLink s ≤ J := fun _ ht =>
    ⟨hLK ht.1, ht.2.1, hLK ht.2.2⟩
  have hJpure : ∀ t ∈ J.faces, ∃ u ∈ J.faces, u.card = 2 ∧ t ⊆ u := by
    intro t ht
    obtain ⟨u, hu, hstu, hucard⟩ := hpure (s ∪ t) ht.2.2
    have hsu : s ⊆ u := Finset.subset_union_left.trans hstu
    have hcard : (u \ s).card = 2 := by
      rw [Finset.card_sdiff_of_subset hsu, hucard, hscard]
    refine ⟨u \ s, ⟨K.down_closed hu Finset.sdiff_subset
      (Finset.card_pos.mp (by omega)), ?_, ?_⟩, hcard, ?_⟩
    · exact Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
    · simpa only [Finset.union_sdiff_of_subset hsu] using hu
    · intro x hx
      exact Finset.mem_sdiff.mpr ⟨hstu (Finset.mem_union_right s hx),
        fun hxs => Finset.disjoint_left.mp ht.2.1 hxs hx⟩
  have hdegree (v : J.vertices) :
      (J.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if s ∪ {v.val} ∈ L.faces then 1 else 2 := by
    rw [K.ncard_faceLink_edgeGraph_neighborSet]
    have hv : v.val ∉ s := (K.faceLink_vertices_subset s v.property).2
    have htri : (s ∪ {v.val}).card = 3 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hv, hscard]
    by_cases h : s ∪ {v.val} ∈ L.faces
    · rw [if_pos h]
      exact (hfacets _ v.property.2.2 Finset.subset_union_left htri).1 h
    · rw [if_neg h]
      exact (hfacets _ v.property.2.2 Finset.subset_union_left htri).2 h
  have hleaf (v : J.vertices) :
      (J.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1 ↔
        v.val ∈ (L.faceLink s).vertices := by
    rw [hdegree]
    by_cases h : s ∪ {v.val} ∈ L.faces
    · rw [if_pos h]
      exact iff_of_true rfl ⟨L.down_closed h Finset.subset_union_right
        (Finset.singleton_nonempty _), v.property.2.1, h⟩
    · rw [if_neg h]
      exact iff_of_false (by omega) (fun hv => h hv.2.2)
  have hendne : (L.faceLink s).vertices.Nonempty := by
    by_contra hn
    have hzero := Set.not_nonempty_iff_eq_empty.mp hn
    rw [hzero, Set.ncard_empty] at hends
    omega
  have hsome : ∃ v : J.vertices,
      (J.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1 := by
    obtain ⟨v, hv⟩ := hendne
    let w : J.vertices := ⟨v, hlinkle hv⟩
    exact ⟨w, (hleaf w).mpr hv⟩
  have hboundary : Subtype.val '' {v : J.vertices |
      (J.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} =
        (L.faceLink s).vertices := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hleaf v).mp hv
    · intro hx
      let v : J.vertices := ⟨x, hlinkle hx⟩
      exact ⟨v, (hleaf v).mpr hx, rfl⟩
  have hLspace : (L.faceLink s).space = (L.faceLink s).vertices := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
      have hcard := hLcard _ ht.2.2
      rw [Finset.card_union_of_disjoint ht.2.1, hscard] at hcard
      have hpos := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht.1)
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
      have hxv : x = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxt
      subst x
      exact ht
    · exact (L.faceLink s).vertices_subset_space
  have hball := J.isFinitePLBallPair_of_pure_edges_with_leaf hJ hJpure
    (J.connected_edgeGraph_of_isConnected hJ hconn)
    (fun v => by rw [hdegree]; split_ifs <;> omega) hsome
  rwa [hboundary, ← hLspace] at hball





theorem isFinitePLBallPair_boundary_edge_link
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hfacets : ∀ t ∈ K.faces, t.card = 3 →
      (t ∈ L.faces → (K.faceLink t).vertices.ncard = 1) ∧
      (t ∉ L.faces → (K.faceLink t).vertices.ncard = 2))
    {s : Finset E} (_hs : s ∈ L.faces) (hscard : s.card = 2)
    (hends : (L.faceLink s).vertices.ncard = 2)
    (hconn : IsConnected (K.faceLink s).space) :
    IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space :=
  K.isFinitePLBallPair_boundary_edge_link_of_local_incidence L hK hLK hpure hLcard
    (fun t ht _ => hfacets t ht) _hs hscard hends hconn

end Geometry.SimplicialComplex
