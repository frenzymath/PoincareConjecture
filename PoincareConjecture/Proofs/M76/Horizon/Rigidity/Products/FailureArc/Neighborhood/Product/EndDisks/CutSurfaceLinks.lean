import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.MarkedArcTriangles
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseLinkSection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.MarkedTriangleComponents
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleCofaceConstancy
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CircleIncidence



set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains PoincareConjecture.M76.Dehn

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] [DecidableEq E] in
private theorem marked_component_le_of_coface_propagation
    (A L J : SimplicialComplex ℝ E)
    (hprop : ∀ s ∈ J.faces, s.card = 2 → s ∉ L.faces →
      ∀ t ∈ A.faces, t.card = 3 → s ⊆ t → t ∈ J.faces)
    (q : Triangle A.toPreAbstractSimplicialComplex) (hq : q.val ∈ J.faces) :
    A.markedTriangleComponent L ((A.markedTriangleGraph L).connectedComponentMk q) ≤ J := by
  intro s hs
  obtain ⟨t,ht,hst⟩ := hs.2
  have hr := ((A.markedTriangleGraph L).connectedComponentMk q).reachable_of_mem_supp
    ht (by simp : q ∈ ((A.markedTriangleGraph L).connectedComponentMk q).supp)
  have hrt := (SimpleGraph.reachable_iff_reflTransGen t q).mp hr
  have hback : ∀ {u}, Relation.ReflTransGen (A.markedTriangleGraph L).Adj u q →
      u.val ∈ J.faces := by
    intro u hu
    induction hu using Relation.ReflTransGen.head_induction_on with
    | refl => exact hq
    | @head a b hab _ ih =>
      obtain ⟨_,u,_,huc,huL,hua,hub⟩ := hab
      exact hprop u (J.down_closed ih hub (Finset.card_pos.mp (by omega)))
        huc huL a.val a.property.1 a.property.2 hua
  exact J.down_closed (hback hrt) hst (A.nonempty_of_mem_faces hs.1)

private theorem subcomplex_link_isConnected_of_rim_arcs
    (A L K : SimplicialComplex ℝ E) [Fintype A.faces]
    (hKA : K ≤ A)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hprop : ∀ s ∈ K.faces, s.card = 2 → s ∉ L.faces →
      ∀ t ∈ A.faces, t.card = 3 → s ⊆ t → t ∈ K.faces)
    {v a b : E} (hvK : v ∈ K.vertices)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v,a} ∈ A.faces) (hb : {v,b} ∈ A.faces)
    (hmarked : ∀ s ∈ L.faces, v ∈ s → s.card = 2 → s = {v,a} ∨ s = {v,b})
    (arc : Bool → Set E)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i)
      {({v,a} : Finset E).centroid ℝ id,({v,b} : Finset E).centroid ℝ id})
    (hcover : arc false ∪ arc true = (A.barycentricSubdivision.link v).space)
    (hinter : arc false ∩ arc true =
      {({v,a} : Finset E).centroid ℝ id,({v,b} : Finset E).centroid ℝ id}) :
    IsConnected (K.link v).space := by
  classical
  let J := K.link v
  have hvA : v ∈ A.vertices := hKA hvK
  obtain ⟨e,_,he⟩ := exists_centroid_vertex_rim_homeomorph A hvA
  have hcentroid (t : Finset E) (ht : t ∈ A.faces) (htc : t.card = 3) (hvt : v ∈ t) :
      t.centroid ℝ id ∈ (A.barycentricSubdivision.link v).space := by
    have htc' : (t.erase v).card = 2 := by simp [Finset.card_erase_of_mem hvt,htc]
    have hs : t.erase v ∈ (A.link v).faces := by
      refine ⟨A.down_closed ht (Finset.erase_subset _ _) (Finset.card_pos.mp (by omega)),
        Finset.notMem_erase _ _,?_⟩
      simpa only [Finset.insert_erase hvt] using ht
    have hval := he (t.erase v) hs
    rw [Finset.insert_erase hvt] at hval
    exact hval ▸ (e _).property
  have hreach (x : J.vertices) : ∃ haJ : a ∈ J.vertices,
      J.vertexAbstractComplex.edgeGraph.Reachable x ⟨a,haJ⟩ := by
    have hxs : insert v ({(x : E)} : Finset E) ∈ K.faces := x.property.2.2
    obtain ⟨t,ht,htc,hst⟩ := hpure _ hxs
    have hvt : v ∈ t := hst (Finset.mem_insert_self _ _)
    have hxt : (x : E) ∈ t := hst (by simp)
    have hct : t.centroid ℝ id ∈ arc false ∪ arc true :=
      hcover.symm ▸ hcentroid t (hKA ht) htc hvt
    obtain ⟨side,hside⟩ : ∃ side : Bool, t.centroid ℝ id ∈ arc side := by
      rcases hct with hct | hct
      · exact ⟨false,hct⟩
      · exact ⟨true,hct⟩
    have hcover' : arc side ∪ arc (!side) = (A.barycentricSubdivision.link v).space := by
      cases side
      · exact hcover
      · simpa only [Bool.not_true,union_comm] using hcover
    have hinter' : arc side ∩ arc (!side) ⊆
        {({v,a} : Finset E).centroid ℝ id,({v,b} : Finset E).centroid ℝ id} := by
      cases side
      · exact hinter.subset
      · simpa only [Bool.not_true,inter_comm] using hinter.subset
    obtain ⟨n,p,hn,hp0,hpn,_,hvp,htri,hwhole⟩ :=
      exists_covering_vertex_arc_triangle_chain A hva hvb hab ha hb (arc side) (arc (!side))
        (hArc side) (hArc (!side)).isCompact.isClosed hcover' hinter'
    let q : Triangle A.toPreAbstractSimplicialComplex := ⟨t,hKA ht,htc⟩
    let C := (A.markedTriangleGraph L).connectedComponentMk q
    have htC : t ∈ (A.markedTriangleComponent L C).faces :=
      (A.markedTriangleComponent_triangle_iff L C q).mpr (by simp [C])
    have hCK := marked_component_le_of_coface_propagation A L K hprop q ht
    have hretained (k : ℕ) (hk : k < n) : {v,p k,p (k+1)} ∈ K.faces :=
      hCK ((vertex_arc_triangles_same_marked_component A L hva hvb hab ha hb hmarked
        (arc side) (arc (!side)) (hArc side) (hArc (!side)).isCompact.isClosed hcover' hinter'
        C (htri k hk).2.1 (htri k hk).2.2.1 (by simp) (htri k hk).2.2.2
        (hKA ht) htc hvt hside).mpr htC)
    have hedge (k : ℕ) (hk : k < n) : {p k,p (k+1)} ∈ J.faces := by
      refine ⟨K.down_closed (hretained k hk) (by simp) (by simp),?_,hretained k hk⟩
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨hvp k hk.le,hvp (k+1) (by omega)⟩
    have hpJ (k : ℕ) (hk : k ≤ n) : p k ∈ J.vertices := by
      by_cases hk' : k < n
      · exact J.down_closed (hedge k hk') (by simp) (by simp)
      · have hkn : k = n := by omega
        have hlast := J.down_closed (hedge (n-1) (by omega))
          (show ({p (n-1+1)} : Finset E) ⊆ {p (n-1),p (n-1+1)} by simp)
          (Finset.singleton_nonempty _)
        change {p k} ∈ J.faces
        simpa only [Nat.sub_add_cancel hn,hkn] using hlast
    have hr (k : ℕ) (hk : k ≤ n) :
        J.vertexAbstractComplex.edgeGraph.Reachable ⟨p 0,hpJ 0 hn.le⟩ ⟨p k,hpJ k hk⟩ := by
      induction k with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ k ih =>
        exact (ih (by omega)).trans (J.reachable_vertices_of_mem_face (hedge k (by omega))
          ⟨p k,hpJ k (by omega)⟩ ⟨p (k+1),hpJ (k+1) hk⟩ (by simp) (by simp))
    obtain ⟨k,hk,htk⟩ := hwhole t (hKA ht) htc hvt hside
    rw [htk] at hxt
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxt
    have hxa : ∃ k ≤ n, (x : E) = p k := by
      rcases hxt with hxv | hxk | hxk
      · exact False.elim (x.property.2.1 (Finset.mem_singleton.mpr hxv.symm))
      · exact ⟨k,hk.le,hxk⟩
      · exact ⟨k+1,by omega,hxk⟩
    obtain ⟨k,hk,hxk⟩ := hxa
    have haJ : a ∈ J.vertices := hp0 ▸ hpJ 0 hn.le
    refine ⟨haJ,?_⟩
    have hx : x = ⟨p k,hpJ k hk⟩ := Subtype.ext hxk
    have h0 : (⟨p 0,hpJ 0 hn.le⟩ : J.vertices) = ⟨a,haJ⟩ := Subtype.ext hp0
    rw [hx,← h0]
    exact (hr k hk).symm
  have hnonempty : Nonempty J.vertices := by
    obtain ⟨t,ht,htc,hvt⟩ := hpure {v} hvK
    have hvt' : v ∈ t := hvt (Finset.mem_singleton_self _)
    have hc : (t.erase v).card = 2 := by simp [Finset.card_erase_of_mem hvt',htc]
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < (t.erase v).card by omega)
    have hxt := Finset.mem_erase.mp hx
    refine ⟨⟨x,K.down_closed ht (Finset.singleton_subset_iff.mpr hxt.2)
      (Finset.singleton_nonempty _),?_,?_⟩⟩
    · simpa only [Finset.mem_singleton] using hxt.1.symm
    · exact K.down_closed ht
        (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
          using And.intro hvt' hxt.2) (by simp)
  let : Nonempty J.vertices := hnonempty
  have hgraph : J.vertexAbstractComplex.edgeGraph.Connected := by
    refine ⟨?_⟩
    intro x y
    obtain ⟨haJ,hx⟩ := hreach x
    obtain ⟨_,hy⟩ := hreach y
    exact hx.trans hy.symm
  exact (J.isPathConnected_space_of_connected_edgeGraph hgraph).isConnected

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem edge_eq_pair_of_mem {s : Finset E} {v : E}
    (hsc : s.card = 2) (hv : v ∈ s) : ∃ a, v ≠ a ∧ s = {v,a} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hsc
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact ⟨b,hab,rfl⟩
  · have he := Finset.mem_singleton.mp hv
    subst v
    exact ⟨a,hab.symm,Finset.pair_comm _ _⟩



theorem closedFaceComplement_links_of_circle_interface
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (gamma : Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ
      (N ⊓ K.closedFaceComplement N).space) (hgamma : gamma.IsFinitePL) :
    ∀ v ∈ (K.closedFaceComplement N).vertices,
      IsConnected ((K.closedFaceComplement N).link v).space := by
  classical
  let C := K.closedFaceComplement N
  let L := N ⊓ C
  have hCK : C ≤ K := K.closedFaceComplement_le N
  have hLK : L ≤ K := fun _ hs ↦ hNK hs.1
  let : Fintype K.faces := hK.fintype
  let : Fintype L.faces := (hK.subset hLK).fintype
  have hinc := Annuli.circle_incidence L (hK.subset hLK) gamma hgamma
  have hprop : ∀ s ∈ C.faces, s.card = 2 → s ∉ L.faces →
      ∀ t ∈ K.faces, t.card = 3 → s ⊆ t → t ∈ C.faces := by
    intro s hs _ hsL t ht _ hst
    have hsN : s ∉ N.faces := fun hsN ↦ hsL ⟨hsN,hs⟩
    exact ⟨ht,t,ht,fun htN ↦ hsN (N.down_closed htN hst
      (C.nonempty_of_mem_faces hs)),subset_rfl⟩
  intro v hvC
  by_cases hvL : v ∈ L.vertices
  · obtain ⟨s₀,s₁,hsne,hsset⟩ := Set.ncard_eq_two.mp (hinc.2.2.2.1 v hvL)
    have hs₀ : s₀ ∈ L.faces ∧ s₀.card = 2 ∧ v ∈ s₀ := by
      exact hsset.symm.subset (Set.mem_insert _ _)
    have hs₁ : s₁ ∈ L.faces ∧ s₁.card = 2 ∧ v ∈ s₁ := by
      exact hsset.symm.subset (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨a,hva,haeq⟩ := edge_eq_pair_of_mem hs₀.2.1 hs₀.2.2
    obtain ⟨b,hvb,hbeq⟩ := edge_eq_pair_of_mem hs₁.2.1 hs₁.2.2
    have hab : a ≠ b := by intro he; exact hsne (haeq.trans (he ▸ hbeq.symm))
    have ha : {v,a} ∈ L.faces := haeq ▸ hs₀.1
    have hb : {v,b} ∈ L.faces := hbeq ▸ hs₁.1
    have hmarked : ∀ s ∈ L.faces, v ∈ s → s.card = 2 → s = {v,a} ∨ s = {v,b} := by
      intro s hs hvs hsc
      have hm : s ∈ ({s₀,s₁} : Set (Finset E)) := hsset ▸ ⟨hs,hsc,hvs⟩
      rcases hm with rfl | rfl
      · exact Or.inl haeq
      · exact Or.inr hbeq
    let edge : Bool → Finset E := fun j ↦ if j then {v,b} else {v,a}
    have hedge (j : Bool) : edge j ∈ L.faces := by cases j; exact ha; exact hb
    have hcard (j : Bool) : (edge j).card = 2 := by
      cases j
      · exact Finset.card_pair hva
      · exact Finset.card_pair hvb
    have hv (j : Bool) : v ∈ edge j := by cases j <;> simp [edge]
    have hne : edge false ≠ edge true := by
      intro he
      have hm : a ∈ edge true := he ▸ (show a ∈ edge false by simp [edge])
      rcases Finset.mem_insert.mp hm with he | he
      · exact hva he.symm
      · exact hab (Finset.mem_singleton.mp he)
    obtain ⟨_,_,_,_,_,U₀,U₁,_,_,hU₀,hU₁,hcover,hinter,_⟩ :=
      exists_boundary_circle_vertex_cut K L hLK hpure hcofaces hinc.1 hvL
        (hlinks v (hCK hvC)) edge hedge hcard hv hne hmarked
    let arc : Bool → Set E := fun j ↦ if j then U₁ else U₀
    have hArc (j : Bool) : IsFinitePLBallPair ℝ (arc j)
        {({v,a} : Finset E).centroid ℝ id,({v,b} : Finset E).centroid ℝ id} := by
      cases j
      · exact hU₀
      · exact hU₁
    exact subcomplex_link_isConnected_of_rim_arcs K L C hCK
      (K.closedFaceComplement_pure N hpure) hprop hvC hva hvb hab
      (hLK ha) (hLK hb) hmarked arc hArc hcover hinter
  · have hvN : v ∉ N.vertices := fun hvN ↦ hvL ⟨hvN,hvC⟩
    have heq : C.link v = K.link v := by
      apply SimplicialComplex.ext
      ext s
      constructor
      · exact fun hs ↦ ⟨hCK hs.1,hs.2.1,hCK hs.2.2⟩
      · intro hs
        have hiN : insert v s ∉ N.faces := fun hi ↦ hvN
          (N.down_closed hi (by simp) (by simp))
        have hiC : insert v s ∈ C.faces :=
          ⟨hs.2.2,insert v s,hs.2.2,hiN,subset_rfl⟩
        exact ⟨C.down_closed hiC (Finset.subset_insert _ _)
          (K.nonempty_of_mem_faces hs.1),hs.2.1,hiC⟩
    rw [heq]
    exact hlinks v (hCK hvC)

open Classical in


theorem closedFaceComplement_incidence_of_circle_interface
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hNpure : ∀ s ∈ N.faces, ∃ t ∈ N.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (gamma : Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ
      (N ⊓ K.closedFaceComplement N).space) (hgamma : gamma.IsFinitePL) :
    (K.closedFaceComplement N).faces.Finite ∧
    (∀ s ∈ (K.closedFaceComplement N).faces,
      ∃ t ∈ (K.closedFaceComplement N).faces, t.card = 3 ∧ s ⊆ t) ∧
    (∀ v ∈ (K.closedFaceComplement N).vertices,
      IsConnected ((K.closedFaceComplement N).link v).space) ∧
    (∀ s ∈ (K.closedFaceComplement N).faces, s.card = 2 →
      {t : Finset E | t ∈ (K.closedFaceComplement N).faces ∧
        t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ (N ⊓ K.closedFaceComplement N).faces then 1 else 2) := by
  classical
  refine ⟨K.closedFaceComplement_finite N hK,K.closedFaceComplement_pure N hpure,
    K.closedFaceComplement_links_of_circle_interface N hK hNK hpure hcofaces hlinks
      gamma hgamma,?_⟩
  intro s hs hsc
  have hm : s ∈ (N ⊓ K.closedFaceComplement N).faces ↔ s ∈ N.faces :=
    ⟨fun h ↦ h.1,fun h ↦ ⟨h,hs⟩⟩
  simpa only [hm] using
    K.closedFaceComplement_edge_coface_count N hK hNK hpure hNpure hcofaces hs hsc

end Geometry.SimplicialComplex
