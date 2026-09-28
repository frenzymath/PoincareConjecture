import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.FiniteIntervalUnion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.IntervalUnionDegree
import PoincareConjecture.Proofs.M76.Mathlib.PureEdgeComplexPolygon
import PoincareConjecture.Proofs.M76.Mathlib.MarkedPolygonArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Resolution
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularOperations
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import Mathlib.SetTheory.Cardinal.NatCard










set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Geometry Topology
namespace PoincareConjecture.M76

theorem exists_polygon_prescribed_arc_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) {U : Set E} {a b : E}
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hUP : U ⊆ P.boundary ℝ) (hab : a ≠ b) :
    ∃ V : Set E,IsFinitePLBallPair ℝ V {a,b} ∧
      U ∪ V = P.boundary ℝ ∧ U ∩ V = {a,b} ∧
      V = P.boundary ℝ \ (U \ {a,b}) := by
  obtain ⟨V,W,hV,hW,hcover,hinter⟩ := P.exists_arcs_at_marks hP hPi
    (hUP (hU.1 (Or.inl rfl))) (hUP (hU.1 (Or.inr rfl))) hab
  have hsub : U \ {a,b} ⊆ V ∪ W := sdiff_subset.trans (hUP.trans hcover.symm.subset)
  have hside : U ⊆ V ∨ U ⊆ W := by
    by_cases hs : U \ {a,b} ⊆ V
    · exact Or.inl (fun x hx => by
        by_cases he : x ∈ ({a,b}:Set E)
        · exact hV.1 he
        · exact hs ⟨hx,he⟩)
    · right
      obtain ⟨x,hx,hxV⟩ := not_subset.mp hs
      have hxW := (hsub hx).resolve_left hxV
      intro y hy
      by_cases he : y ∈ ({a,b}:Set E)
      · exact hW.1 he
      · by_contra hyW
        have hyV := (hsub ⟨hy,he⟩).resolve_right hyW
        obtain ⟨z,hz,hzVW⟩ := isPreconnected_closed_iff.mp hU.isConnected_sdiff.isPreconnected
          V W hV.isCompact.isClosed hW.isCompact.isClosed hsub
          ⟨y,⟨hy,he⟩,hyV⟩ ⟨x,hx,hxW⟩
        exact hz.2 (hinter.subset hzVW)
  have hfinish {V : Set E} (hV : IsFinitePLBallPair ℝ V {a,b})
      (hc : U ∪ V = P.boundary ℝ) (hi : U ∩ V = {a,b}) :
      V = P.boundary ℝ \ (U \ {a,b}) := by
    ext x
    constructor
    · intro hx
      refine ⟨hc.subset (Or.inr hx),?_⟩
      exact fun h => h.2 (hi.subset ⟨h.1,hx⟩)
    · intro hx
      rcases hc.symm.subset hx.1 with hxU | hxV
      · exact hV.1 (by by_contra hn; exact hx.2 ⟨hxU,hn⟩)
      · exact hxV
  rcases hside with hs | hs
  · have heq := hU.eq_of_subset_with_same_endpoints hV hs hab
    have hc : U ∪ W = P.boundary ℝ := heq.symm ▸ hcover
    have hi : U ∩ W = {a,b} := heq.symm ▸ hinter
    exact ⟨W,hW,hc,hi,hfinish hW hc hi⟩
  · have heq := hU.eq_of_subset_with_same_endpoints hW hs hab
    have hc : U ∪ V = P.boundary ℝ := by rw [heq,union_comm]; exact hcover
    have hi : U ∩ V = {a,b} := by rw [heq,inter_comm]; exact hinter
    exact ⟨V,hV,hc,hi,hfinish hV hc hi⟩

theorem exists_four_interval_cycle_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (v : Fin 4 → E) (hvi : Function.Injective v) (D : Fin 4 → Set E)
    (hD : ∀ i,IsFinitePLBallPair ℝ (D i) {v i,v (finRotate 4 i)})
    (hinter : ∀ i j,i ≠ j → D i ∩ D j ⊆
      ({v i,v (finRotate 4 i)} : Set E) ∩ {v j,v (finRotate 4 j)}) :
    ∃ G : SimplicialComplex ℝ E,G.faces.Finite ∧ G.space = ⋃ i,D i ∧
      (∀ s ∈ G.faces,s.card ≤ 2) ∧
      (∀ x : G.vertices,(G.vertexAbstractComplex.edgeGraph.neighborSet x).ncard = 2) ∧
      ∃ n,∃ P : Polygon E (n+3),Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = G.space := by
  classical
  let R : Fin 4 → Set E := fun i => {v i,v (finRotate 4 i)}
  have hend : ∀ p ∈ ⋃ i,R i,{i | p ∈ R i}.ncard = 2 := by
    intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    have hex : ∃ j,p = v j := by
      rcases hi with h | h
      · exact ⟨i,h⟩
      · exact ⟨finRotate 4 i,h⟩
    obtain ⟨j,rfl⟩ := hex
    have heq : {i | v j ∈ R i} = {j,(finRotate 4).symm j} := by
      ext i
      simp only [R,mem_ofPred_eq,mem_insert_iff,mem_singleton_iff,hvi.eq_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr ((finRotate 4).symm_apply_eq.mpr h).symm
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr ((finRotate 4).apply_symm_apply j).symm
    have hn : j ≠ (finRotate 4).symm j := by fin_cases j <;> decide
    rw [heq]
    exact ncard_pair hn
  obtain ⟨G,hG,hGs,hGdim,_⟩ := exists_finite_interval_union_complex D R hD
  have hdeg := interval_union_graph_degree_two D R hD hinter hend G hG hGdim hGs
  have h01 : IsConnected (D 0 ∪ D 1) := (hD 0).isConnected.union
    ⟨v 1,by simpa using (hD 0).1 (Or.inr rfl),(hD 1).1 (Or.inl rfl)⟩ (hD 1).isConnected
  have h012 : IsConnected ((D 0 ∪ D 1) ∪ D 2) := h01.union
    ⟨v 2,Or.inr (by simpa using (hD 1).1 (Or.inr rfl)),(hD 2).1 (Or.inl rfl)⟩ (hD 2).isConnected
  have hall : IsConnected (((D 0 ∪ D 1) ∪ D 2) ∪ D 3) := h012.union
    ⟨v 3,Or.inr (by simpa using (hD 2).1 (Or.inr rfl)),(hD 3).1 (Or.inl rfl)⟩ (hD 3).isConnected
  have hunion : ((D 0 ∪ D 1) ∪ D 2) ∪ D 3 = ⋃ i,D i := by
    ext x
    simp only [mem_union,mem_iUnion]
    constructor
    · rintro (((h | h) | h) | h)
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
      · exact ⟨3,h⟩
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (Or.inl hi))
      · exact Or.inl (Or.inl (Or.inr hi))
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
  have hconn : IsConnected G.space := hGs.symm ▸ (hunion ▸ hall)
  have hpure : ∀ s ∈ G.faces,∃ t ∈ G.faces,t.card = 2 ∧ s ⊆ t := by
    intro s hs
    by_cases htwo : s.card = 2
    · exact ⟨s,hs,htwo,Subset.rfl⟩
    have hone : s.card = 1 := by
      have := hGdim s hs
      have := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
      omega
    obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hone
    let v : G.vertices := ⟨a,hs⟩
    have hne : (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
      by_contra hn
      have hz := not_nonempty_iff_eq_empty.mp hn
      have hh := hdeg v
      rw [hz,ncard_empty] at hh
      omega
    obtain ⟨w,hw⟩ := hne
    have hne' : a ≠ (w : E) := fun h => hw.1 (Subtype.ext h)
    have hedge := hw.2
    change ({v,w} : Finset G.vertices).map (Function.Embedding.subtype _) ∈ G.faces at hedge
    have ht : ({a,(w:E)} : Finset E) ∈ G.faces := by
      simpa only [Finset.map_insert,Finset.map_singleton,Function.Embedding.coe_subtype] using hedge
    exact ⟨{a,(w:E)},ht,by simp [hne'],by simp⟩
  obtain ⟨n,P,hPi,hP,hPG⟩ := G.exists_polygon_of_pure_edges hG hpure
    (G.connected_edgeGraph_of_isConnected hG hconn) hdeg
  exact ⟨G,hG,hGs,hGdim,hdeg,n,P,hPi,hP,hPG⟩

theorem exists_polygon_of_two_circle_band
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {n m : ℕ} (P : Polygon E (n+3)) (Q : Polygon E (m+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hPQ : Disjoint (P.boundary ℝ) (Q.boundary ℝ))
    (v : Fin 4 → E) (hvi : Function.Injective v) (U V W Z : Set E)
    (hU : IsFinitePLBallPair ℝ U {v 0,v 1})
    (hV : IsFinitePLBallPair ℝ V {v 2,v 3})
    (hW : IsFinitePLBallPair ℝ W {v 1,v 2})
    (hZ : IsFinitePLBallPair ℝ Z {v 3,v 0})
    (hUP : U ⊆ P.boundary ℝ) (hVQ : V ⊆ Q.boundary ℝ)
    (hWO : W ∩ (P.boundary ℝ ∪ Q.boundary ℝ) = {v 1,v 2})
    (hZO : Z ∩ (P.boundary ℝ ∪ Q.boundary ℝ) = {v 3,v 0})
    (hWZ : Disjoint W Z) :
    ∃ G : SimplicialComplex ℝ E,G.faces.Finite ∧
      G.space = ((P.boundary ℝ ∪ Q.boundary ℝ) \
        ((U \ {v 0,v 1}) ∪ (V \ {v 2,v 3}))) ∪ (W ∪ Z) ∧
      (∀ s ∈ G.faces,s.card ≤ 2) ∧
      (∀ x : G.vertices,(G.vertexAbstractComplex.edgeGraph.neighborSet x).ncard = 2) ∧
      ∃ k,∃ L : Polygon E (k+3),Function.Injective L ∧ L.HasSimplicialEdges ∧
        L.boundary ℝ = G.space := by
  classical
  obtain ⟨A,hA,hUA,hUAi,hAe⟩ := exists_polygon_prescribed_arc_complement
    P hP hPi hU hUP (hvi.ne (by decide))
  obtain ⟨B,hB,hVB,hVBi,hBe⟩ := exists_polygon_prescribed_arc_complement
    Q hQ hQi hV hVQ (hvi.ne (by decide))
  have hAP : A ⊆ P.boundary ℝ := fun x hx => hUA.subset (Or.inr hx)
  have hBQ : B ⊆ Q.boundary ℝ := fun x hx => hVB.subset (Or.inr hx)
  have h0P := hUP (hU.1 (Or.inl rfl))
  have h1P := hUP (hU.1 (Or.inr rfl))
  have h2Q := hVQ (hV.1 (Or.inl rfl))
  have h3Q := hVQ (hV.1 (Or.inr rfl))
  have hAW : A ∩ W ⊆ {v 1} := by
    rintro x ⟨hxA,hxW⟩
    rcases hWO.subset ⟨hxW,Or.inl (hAP hxA)⟩ with h | h
    · exact h
    · exact (disjoint_left.mp hPQ (hAP hxA) (h ▸ h2Q)).elim
  have hAZ : A ∩ Z ⊆ {v 0} := by
    rintro x ⟨hxA,hxZ⟩
    rcases hZO.subset ⟨hxZ,Or.inl (hAP hxA)⟩ with h | h
    · exact (disjoint_left.mp hPQ (hAP hxA) (h ▸ h3Q)).elim
    · exact h
  have hBW : B ∩ W ⊆ {v 2} := by
    rintro x ⟨hxB,hxW⟩
    rcases hWO.subset ⟨hxW,Or.inr (hBQ hxB)⟩ with h | h
    · exact (disjoint_left.mp hPQ (h ▸ h1P) (hBQ hxB)).elim
    · exact h
  have hBZ : B ∩ Z ⊆ {v 3} := by
    rintro x ⟨hxB,hxZ⟩
    rcases hZO.subset ⟨hxZ,Or.inr (hBQ hxB)⟩ with h | h
    · exact h
    · exact (disjoint_left.mp hPQ (h ▸ h0P) (hBQ hxB)).elim
  have hAB : Disjoint A B := hPQ.mono hAP hBQ
  let D : Fin 4 → Set E := ![A,W,B,Z]
  have hD : ∀ i,IsFinitePLBallPair ℝ (D i) {v i,v (finRotate 4 i)} := by
    intro i
    fin_cases i <;> simpa [D] using (by assumption : IsFinitePLBallPair ℝ _ _)
  have hinter : ∀ i j,i ≠ j → D i ∩ D j ⊆
      ({v i,v (finRotate 4 i)} : Set E) ∩ {v j,v (finRotate 4 j)} := by
    intro i j hij x hx
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · have he : x = v 1 := hAW hx
      simp [he]
    · exact (disjoint_left.mp hAB hx.1 hx.2).elim
    · have he : x = v 0 := hAZ hx
      simp [he]
    · have he : x = v 1 := hAW ⟨hx.2,hx.1⟩
      simp [he]
    · exact (hij rfl).elim
    · have he : x = v 2 := hBW ⟨hx.2,hx.1⟩
      simp [he]
    · exact (disjoint_left.mp hWZ hx.1 hx.2).elim
    · exact (disjoint_left.mp hAB hx.2 hx.1).elim
    · have he : x = v 2 := hBW hx
      simp [he]
    · exact (hij rfl).elim
    · have he : x = v 3 := hBZ hx
      simp [he]
    · have he : x = v 0 := hAZ ⟨hx.2,hx.1⟩
      simp [he]
    · exact (disjoint_left.mp hWZ hx.2 hx.1).elim
    · have he : x = v 3 := hBZ ⟨hx.2,hx.1⟩
      simp [he]
    · exact (hij rfl).elim
  obtain ⟨G,hG,hGs,hdim,hdeg,k,L,hLi,hL,hLG⟩ :=
    exists_four_interval_cycle_graph v hvi D hD hinter
  have hspace : (⋃ i,D i) = ((P.boundary ℝ ∪ Q.boundary ℝ) \
      ((U \ {v 0,v 1}) ∪ (V \ {v 2,v 3}))) ∪ (W ∪ Z) := by
    have hUV : Disjoint U V := hPQ.mono hUP hVQ
    have hPV : Disjoint (P.boundary ℝ) V := hPQ.mono_right hVQ
    have hQU : Disjoint (Q.boundary ℝ) U := hPQ.symm.mono_right hUP
    have hDu : (⋃ i,D i) = A ∪ W ∪ B ∪ Z := by
      ext x
      simp only [mem_iUnion,mem_union]
      constructor
      · rintro ⟨i,hi⟩
        fin_cases i
        · exact Or.inl (Or.inl (Or.inl hi))
        · exact Or.inl (Or.inl (Or.inr hi))
        · exact Or.inl (Or.inr hi)
        · exact Or.inr hi
      · rintro (((h | h) | h) | h)
        · exact ⟨0,h⟩
        · exact ⟨1,h⟩
        · exact ⟨2,h⟩
        · exact ⟨3,h⟩
    rw [hDu]
    rw [hAe,hBe]
    ext x
    simp only [mem_union,mem_sdiff,mem_insert_iff,mem_singleton_iff]
    have hpv : x ∈ P.boundary ℝ → x ∈ V → False := fun hp hv => disjoint_left.mp hPV hp hv
    have hqu : x ∈ Q.boundary ℝ → x ∈ U → False := fun hq hu => disjoint_left.mp hQU hq hu
    tauto
  exact ⟨G,hG,hGs.trans hspace,hdim,hdeg,k,L,hLi,hL,hLG⟩

theorem component_count_after_two_component_merge
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hclosed : ∀ i,IsClosed (C i))
    (hconn : ∀ i,IsConnected (C i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (i j : I) (hij : i ≠ j) {Q : Set X} (hQc : IsClosed Q)
    (hQ : IsConnected Q)
    (hQdis : ∀ k,k ≠ i → k ≠ j → Disjoint Q (C k)) :
    Nat.card (ConnectedComponents ↥(Q ∪ ⋃ k : {k : I // k ≠ i ∧ k ≠ j},C k)) + 1 =
      Nat.card (ConnectedComponents ↥(⋃ k,C k)) := by
  classical
  let J := {k : I // k ≠ i ∧ k ≠ j}
  let N : Option J → Set X
    | none => Q
    | some k => C k
  have hNc : ∀ k,IsClosed (N k) := by
    rintro (_ | k)
    · exact hQc
    · exact hclosed k
  have hNconn : ∀ k,IsConnected (N k) := by
    rintro (_ | k)
    · exact hQ
    · exact hconn k
  have hNd : Pairwise fun k l => Disjoint (N k) (N l) := by
    rintro (_ | k) (_ | l) hkl
    · exact (hkl rfl).elim
    · exact hQdis l l.property.1 l.property.2
    · exact (hQdis k k.property.1 k.property.2).symm
    · exact hdis (fun h => hkl (congrArg some (Subtype.ext h)))
  have hNcover : (⋃ k,N k) = Q ∪ ⋃ k : J,C k := by
    rw [iUnion_option]
  rw [Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    N hNc hNconn hNd hNcover,
    Poincare.Topology.card_connectedComponents_of_finite_closed_cover
      C hclosed hconn hdis rfl,Finite.card_option]
  let _ := Fintype.ofFinite I
  have htwo : Nat.card {k : I // k = i ∨ k = j} = 2 := by
    change ({k : I | k = i ∨ k = j} : Set I).ncard = 2
    convert ncard_pair hij using 1
    congr 1
  have hcount : Nat.card J = Nat.card I - 2 := by
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    simpa only [not_or,ne_eq,← Nat.card_eq_fintype_card,htwo] using
      Fintype.card_subtype_compl (fun k : I => k = i ∨ k = j)
  have hle : 2 ≤ Nat.card I := by
    rw [← htwo,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  omega

theorem polygon_presentation_after_two_component_merge
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
    (n : I → ℕ) (P : ∀ k,Polygon E (n k+3))
    (hP : ∀ k,Function.Injective (P k) ∧ (P k).HasSimplicialEdges)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (i j : I) {m : ℕ} (Q : Polygon E (m+3))
    (hQi : Function.Injective Q) (hQ : Q.HasSimplicialEdges)
    (hQdis : ∀ k,k ≠ i → k ≠ j → Disjoint (Q.boundary ℝ) ((P k).boundary ℝ)) :
    HasDisjointPolygonPresentation
      (Q.boundary ℝ ∪ ⋃ k : {k : I // k ≠ i ∧ k ≠ j},(P k).boundary ℝ) := by
  have hrest : HasDisjointPolygonPresentation
      (⋃ k : {k : I // k ≠ i ∧ k ≠ j},(P k).boundary ℝ) := by
    exact hasDisjointPolygonPresentation_of_family
      (fun k : {k : I // k ≠ i ∧ k ≠ j} => n k) (fun k => P k)
      (fun k => hP k) rfl (fun (k l : {k : I // k ≠ i ∧ k ≠ j}) hkl =>
        hdis (fun h => hkl (Subtype.ext h)))
  exact hrest.union_polygon Q hQi hQ (disjoint_iUnion_right.mpr
    (fun k => hQdis k k.property.1 k.property.2))

theorem exists_degree_two_graph_of_polygon_presentation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {S : Set E} (hS : HasDisjointPolygonPresentation S) :
    ∃ G : SimplicialComplex ℝ E,G.faces.Finite ∧ G.space = S ∧
      (∀ s ∈ G.faces,s.card ≤ 2) ∧
      ∀ x : G.vertices,(G.vertexAbstractComplex.edgeGraph.neighborSet x).ncard = 2 := by
  classical
  obtain ⟨m,n,P,hP,hcover,hdis⟩ := hS
  have hex (i : Fin m) := (P i).exists_arcs_at_marks (hP i).2 (hP i).1
    ((P i).vertex_mem_boundary 0) ((P i).vertex_mem_boundary 1)
    ((hP i).1.ne (by norm_num))
  choose A B hA hB hAB hABi using hex
  let D : Fin m × Bool → Set E := fun k => if k.2 then B k.1 else A k.1
  let R : Fin m × Bool → Set E := fun k => {(P k.1) 0,(P k.1) 1}
  have hD (k : Fin m × Bool) : IsFinitePLBallPair ℝ (D k) (R k) := by
    rcases k with ⟨i,b⟩
    cases b
    · exact hA i
    · exact hB i
  have hDP (k : Fin m × Bool) : D k ⊆ (P k.1).boundary ℝ := by
    rcases k with ⟨i,b⟩
    cases b
    · exact fun x hx => (hAB i).subset (Or.inl hx)
    · exact fun x hx => (hAB i).subset (Or.inr hx)
  have hRP (k : Fin m × Bool) : R k ⊆ (P k.1).boundary ℝ := (hD k).1.trans (hDP k)
  have hinter : ∀ i j,i ≠ j → D i ∩ D j ⊆ R i ∩ R j := by
    rintro ⟨i,b⟩ ⟨j,c⟩ hij x ⟨hx,hy⟩
    by_cases he : i = j
    · subst j
      have hr : x ∈ ({(P i) 0,(P i) 1} : Set E) := by
        cases b <;> cases c
        · exact (hij rfl).elim
        · exact (hABi i).subset ⟨hx,hy⟩
        · exact (hABi i).subset ⟨hy,hx⟩
        · exact (hij rfl).elim
      exact ⟨hr,hr⟩
    · exact (disjoint_left.mp (hdis he) (hDP ⟨i,b⟩ hx) (hDP ⟨j,c⟩ hy)).elim
  have hend : ∀ p ∈ ⋃ i,R i,{i | p ∈ R i}.ncard = 2 := by
    intro p hp
    obtain ⟨⟨i,b⟩,hi⟩ := mem_iUnion.mp hp
    have heq : {k | p ∈ R k} = {(i,false),(i,true)} := by
      ext ⟨j,c⟩
      constructor
      · intro hj
        have hji : j = i := by
          by_contra h
          exact disjoint_left.mp (hdis h) (hRP ⟨j,c⟩ hj) (hRP ⟨i,b⟩ hi)
        subst j
        cases c <;> simp
      · intro hj
        rcases hj with h | h <;> cases h <;> exact hi
    rw [heq]
    exact ncard_pair (by simp)
  have hDs : (⋃ k,D k) = S := by
    rw [hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion_of_mem k.1 (hDP k hk)
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      rcases (hAB i).symm.subset hi with ha | hb
      · exact mem_iUnion_of_mem (i,false) ha
      · exact mem_iUnion_of_mem (i,true) hb
  obtain ⟨G,hG,hGs,hdim,_⟩ := exists_finite_interval_union_complex D R hD
  exact ⟨G,hG,hGs.trans hDs,hdim,
    interval_union_graph_degree_two D R hD hinter hend G hG hdim hGs⟩

theorem exists_spanning_band_contact_graph
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [Finite I]
    (n : I → ℕ) (P : ∀ k,Polygon E (n k+3))
    (hP : ∀ k,Function.Injective (P k) ∧ (P k).HasSimplicialEdges)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (i j : I) (hij : i ≠ j) (v : Fin 4 → E) (hvi : Function.Injective v)
    (U V W Z : Set E)
    (hU : IsFinitePLBallPair ℝ U {v 0,v 1})
    (hV : IsFinitePLBallPair ℝ V {v 2,v 3})
    (hW : IsFinitePLBallPair ℝ W {v 1,v 2})
    (hZ : IsFinitePLBallPair ℝ Z {v 3,v 0})
    (hUP : U ⊆ (P i).boundary ℝ) (hVQ : V ⊆ (P j).boundary ℝ)
    (hWO : W ∩ (⋃ k,(P k).boundary ℝ) = {v 1,v 2})
    (hZO : Z ∩ (⋃ k,(P k).boundary ℝ) = {v 3,v 0})
    (hWZ : Disjoint W Z) :
    ∃ G : SimplicialComplex ℝ E,G.faces.Finite ∧
      G.space = ((⋃ k,(P k).boundary ℝ) \
        ((U \ {v 0,v 1}) ∪ (V \ {v 2,v 3}))) ∪ (W ∪ Z) ∧
      HasDisjointPolygonPresentation G.space ∧
      (∀ s ∈ G.faces,s.card ≤ 2) ∧
      (∀ x : G.vertices,(G.vertexAbstractComplex.edgeGraph.neighborSet x).ncard = 2) ∧
      Nat.card (ConnectedComponents G.space) + 1 =
        Nat.card (ConnectedComponents ↥(⋃ k,(P k).boundary ℝ)) := by
  classical
  let C : I → Set E := fun k => (P k).boundary ℝ
  have h0P : v 0 ∈ C i := hUP (hU.1 (Or.inl rfl))
  have h1P : v 1 ∈ C i := hUP (hU.1 (Or.inr rfl))
  have h2Q : v 2 ∈ C j := hVQ (hV.1 (Or.inl rfl))
  have h3Q : v 3 ∈ C j := hVQ (hV.1 (Or.inr rfl))
  have hpairsub : C i ∪ C j ⊆ ⋃ k,C k := union_subset
    (subset_iUnion _ i) (subset_iUnion _ j)
  have hWO' : W ∩ (C i ∪ C j) = {v 1,v 2} := by
    apply Subset.antisymm ((inter_subset_inter_right W hpairsub).trans hWO.subset)
    rintro x (rfl | rfl)
    · exact ⟨hW.1 (Or.inl rfl),Or.inl h1P⟩
    · exact ⟨hW.1 (Or.inr rfl),Or.inr h2Q⟩
  have hZO' : Z ∩ (C i ∪ C j) = {v 3,v 0} := by
    apply Subset.antisymm ((inter_subset_inter_right Z hpairsub).trans hZO.subset)
    rintro x (rfl | rfl)
    · exact ⟨hZ.1 (Or.inl rfl),Or.inr h3Q⟩
    · exact ⟨hZ.1 (Or.inr rfl),Or.inl h0P⟩
  obtain ⟨H,hH,hHs,_,_,k,L,hLi,hL,hLH⟩ := exists_polygon_of_two_circle_band
    (P i) (P j) (hP i).2 (hP i).1 (hP j).2 (hP j).1 (hdis hij)
    v hvi U V W Z hU hV hW hZ hUP hVQ hWO' hZO' hWZ
  let T : Set E := ⋃ k : {k : I // k ≠ i ∧ k ≠ j},C k
  let A : Set E := (U \ {v 0,v 1}) ∪ (V \ {v 2,v 3})
  have hLset : L.boundary ℝ = ((C i ∪ C j) \ A) ∪ (W ∪ Z) := hLH.trans hHs
  have hside (l : I) (hli : l ≠ i) (hlj : l ≠ j) : Disjoint (W ∪ Z) (C l) := by
    apply disjoint_left.mpr
    rintro x (hxW | hxZ) hxl
    · rcases hWO.subset ⟨hxW,mem_iUnion_of_mem l hxl⟩ with h | h
      · exact disjoint_left.mp (hdis hli) hxl (h ▸ h1P)
      · exact disjoint_left.mp (hdis hlj) hxl (h ▸ h2Q)
    · rcases hZO.subset ⟨hxZ,mem_iUnion_of_mem l hxl⟩ with h | h
      · exact disjoint_left.mp (hdis hlj) hxl (h ▸ h3Q)
      · exact disjoint_left.mp (hdis hli) hxl (h ▸ h0P)
  have hLdis (l : I) (hli : l ≠ i) (hlj : l ≠ j) : Disjoint (L.boundary ℝ) (C l) := by
    rw [hLset]
    exact ((hdis hli).symm.union_left (hdis hlj).symm).mono_left sdiff_subset |>.union_left
      (hside l hli hlj)
  have hpres : HasDisjointPolygonPresentation (L.boundary ℝ ∪ T) :=
    polygon_presentation_after_two_component_merge n P hP hdis i j L hLi hL hLdis
  have hwhole : (⋃ k,C k) = (C i ∪ C j) ∪ T := by
    ext x
    constructor
    · intro hx
      obtain ⟨l,hl⟩ := mem_iUnion.mp hx
      by_cases hli : l = i
      · exact Or.inl (Or.inl (hli ▸ hl))
      by_cases hlj : l = j
      · exact Or.inl (Or.inr (hlj ▸ hl))
      · exact Or.inr (mem_iUnion_of_mem ⟨l,hli,hlj⟩ hl)
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion_of_mem i hx
      · exact mem_iUnion_of_mem j hx
      · obtain ⟨l,hl⟩ := mem_iUnion.mp hx
        exact mem_iUnion_of_mem l.val hl
  have hTA : Disjoint T A := by
    apply disjoint_left.mpr
    intro x hx hxa
    obtain ⟨l,hl⟩ := mem_iUnion.mp hx
    rcases hxa with hu | hv
    · exact disjoint_left.mp (hdis l.property.1) hl (hUP hu.1)
    · exact disjoint_left.mp (hdis l.property.2) hl (hVQ hv.1)
  have hnew : L.boundary ℝ ∪ T = ((⋃ k,C k) \ A) ∪ (W ∪ Z) := by
    rw [hLset,hwhole]
    ext x
    have hta : x ∈ T → x ∉ A := fun ht => disjoint_left.mp hTA ht
    simp only [mem_union,mem_sdiff]
    tauto
  have hconn (l : I) : IsConnected (C l) := by
    obtain ⟨e⟩ := (P l).nonempty_boundary_homeomorph_circle (hP l).2 (hP l).1
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hLconn : IsConnected (L.boundary ℝ) := by
    obtain ⟨e⟩ := L.nonempty_boundary_homeomorph_circle hL hLi
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hcount := component_count_after_two_component_merge C
    (fun l => (P l).isClosed_boundary) hconn hdis i j hij L.isClosed_boundary hLconn hLdis
  obtain ⟨G,hG,hGs,hdim,hdeg⟩ := exists_degree_two_graph_of_polygon_presentation hpres
  exact ⟨G,hG,hGs.trans hnew,hGs.symm ▸ hpres,hdim,hdeg,hGs.symm ▸ hcount⟩

end PoincareConjecture.M76

