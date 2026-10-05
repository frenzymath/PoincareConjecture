import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surfaces.MarkedArcTriangles
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderBaseLinkSection

/-!
# Connected links at actual marked vertices of the cut

Every retained triangle lies on one of the two actual vertex rim arcs.
The whole triangle chain of that arc is retained, and connects each of its
link vertices to the same marked endpoint. Thus no disconnected vertex
link is introduced by taking a component of the marked triangle graph.
-/

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex
open PoincareMT.M76.Dehn

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- The two constructed interval arcs imply connectedness of the actual
selected component's full vertex link. -/
theorem markedTriangleComponent_link_isConnected_of_rim_arcs
    (A L : SimplicialComplex ℝ E) [Fintype A.faces]
    (C : (A.markedTriangleGraph L).ConnectedComponent)
    {v a b : E} (hvC : v ∈ (A.markedTriangleComponent L C).vertices)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v, a} ∈ A.faces) (hb : {v, b} ∈ A.faces)
    (hmarked : ∀ s ∈ L.faces, v ∈ s → s.card = 2 → s = {v, a} ∨ s = {v, b})
    (arc : Bool → Set E)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i)
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id})
    (hcover : arc false ∪ arc true = (A.barycentricSubdivision.link v).space)
    (hinter : arc false ∩ arc true =
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id}) :
    IsConnected ((A.markedTriangleComponent L C).link v).space := by
  classical
  let K := A.markedTriangleComponent L C
  let J := K.link v
  have hvA : v ∈ A.vertices := hvC.1
  obtain ⟨e, _, he⟩ := exists_centroid_vertex_rim_homeomorph A hvA
  have hcentroid (t : Finset E) (ht : t ∈ A.faces) (htc : t.card = 3) (hvt : v ∈ t) :
      t.centroid ℝ id ∈ (A.barycentricSubdivision.link v).space := by
    have htc' : (t.erase v).card = 2 := by simp [Finset.card_erase_of_mem hvt, htc]
    have hs : t.erase v ∈ (A.link v).faces := by
      refine ⟨A.down_closed ht (Finset.erase_subset _ _)
        (Finset.card_pos.mp (by omega)), Finset.notMem_erase _ _, ?_⟩
      simpa only [Finset.insert_erase hvt] using ht
    have hval := he (t.erase v) hs
    rw [Finset.insert_erase hvt] at hval
    exact hval ▸ (e _).property
  have hreach (x : J.vertices) : ∃ haJ : a ∈ J.vertices,
      J.vertexAbstractComplex.edgeGraph.Reachable x ⟨a, haJ⟩ := by
    have hxs : insert v ({(x : E)} : Finset E) ∈ K.faces := x.property.2.2
    obtain ⟨t, ht, htc, hst⟩ := A.markedTriangleComponent_pure L C _ hxs
    have hvt : v ∈ t := hst (Finset.mem_insert_self _ _)
    have hxt : (x : E) ∈ t := hst (by simp)
    have hct : t.centroid ℝ id ∈ arc false ∪ arc true :=
      hcover.symm ▸ hcentroid t ht.1 htc hvt
    obtain ⟨side, hside⟩ : ∃ side : Bool, t.centroid ℝ id ∈ arc side := by
      rcases hct with hct | hct
      · exact ⟨false, hct⟩
      · exact ⟨true, hct⟩
    have hcover' : arc side ∪ arc (!side) = (A.barycentricSubdivision.link v).space := by
      cases side
      · exact hcover
      · simpa only [Bool.not_true, union_comm] using hcover
    have hinter' : arc side ∩ arc (!side) ⊆
        {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id} := by
      cases side
      · exact hinter.subset
      · simpa only [Bool.not_true, inter_comm] using hinter.subset
    obtain ⟨n, p, hn, hp0, hpn, hpi, hvp, htri, hwhole⟩ :=
      exists_covering_vertex_arc_triangle_chain A hva hvb hab ha hb (arc side) (arc (!side))
        (hArc side) (hArc (!side)).isCompact.isClosed hcover' hinter'
    have hretained (k : ℕ) (hk : k < n) : {v, p k, p (k + 1)} ∈ K.faces :=
      (vertex_arc_triangles_same_marked_component A L hva hvb hab ha hb hmarked
        (arc side) (arc (!side)) (hArc side) (hArc (!side)).isCompact.isClosed hcover' hinter'
        C (htri k hk).2.1 (htri k hk).2.2.1 (by simp) (htri k hk).2.2.2
        ht.1 htc hvt hside).mpr ht
    have hedge (k : ℕ) (hk : k < n) : {p k, p (k + 1)} ∈ J.faces := by
      refine ⟨K.down_closed (hretained k hk) (by simp) (by simp), ?_, hretained k hk⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvp k hk.le, hvp (k + 1) (by omega)⟩
    have hpJ (k : ℕ) (hk : k ≤ n) : p k ∈ J.vertices := by
      by_cases hk' : k < n
      · exact J.down_closed (hedge k hk') (by simp) (by simp)
      · have hkn : k = n := by omega
        have hlast := J.down_closed (hedge (n - 1) (by omega))
          (show ({p (n - 1 + 1)} : Finset E) ⊆ {p (n - 1), p (n - 1 + 1)} by simp)
          (Finset.singleton_nonempty _)
        change {p k} ∈ J.faces
        simpa only [Nat.sub_add_cancel hn, hkn] using hlast
    have hr (k : ℕ) (hk : k ≤ n) :
        J.vertexAbstractComplex.edgeGraph.Reachable ⟨p 0, hpJ 0 hn.le⟩ ⟨p k, hpJ k hk⟩ := by
      induction k with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ k ih =>
        exact (ih (by omega)).trans (J.reachable_vertices_of_mem_face (hedge k (by omega))
          ⟨p k, hpJ k (by omega)⟩ ⟨p (k + 1), hpJ (k + 1) hk⟩ (by simp) (by simp))
    obtain ⟨k, hk, htk⟩ := hwhole t ht.1 htc hvt hside
    rw [htk] at hxt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    have hxa : ∃ k ≤ n, (x : E) = p k := by
      rcases hxt with hxv | hxk | hxk
      · exact False.elim (x.property.2.1 (Finset.mem_singleton.mpr hxv.symm))
      · exact ⟨k, hk.le, hxk⟩
      · exact ⟨k + 1, by omega, hxk⟩
    obtain ⟨k, hk, hxk⟩ := hxa
    have haJ : a ∈ J.vertices := hp0 ▸ hpJ 0 hn.le
    refine ⟨haJ, ?_⟩
    have hx : x = ⟨p k, hpJ k hk⟩ := Subtype.ext hxk
    have h0 : (⟨p 0, hpJ 0 hn.le⟩ : J.vertices) = ⟨a, haJ⟩ := Subtype.ext hp0
    rw [hx, ← h0]
    exact (hr k hk).symm
  have hnonempty : Nonempty J.vertices := by
    obtain ⟨t, ht, htc, hvt⟩ := A.markedTriangleComponent_pure L C {v} hvC
    have hvt' : v ∈ t := hvt (Finset.mem_singleton_self _)
    have hc : (t.erase v).card = 2 := by simp [Finset.card_erase_of_mem hvt', htc]
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (t.erase v).card by omega)
    have hxt := Finset.mem_erase.mp hx
    refine ⟨⟨x, K.down_closed ht (Finset.singleton_subset_iff.mpr hxt.2)
      (Finset.singleton_nonempty _), ?_, ?_⟩⟩
    · simpa only [Finset.mem_singleton] using hxt.1.symm
    · exact K.down_closed ht
        (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          using And.intro hvt' hxt.2) (by simp)
  let : Nonempty J.vertices := hnonempty
  have hgraph : J.vertexAbstractComplex.edgeGraph.Connected := by
    refine ⟨?_⟩
    intro x y
    obtain ⟨haJ, hx⟩ := hreach x
    obtain ⟨_, hy⟩ := hreach y
    exact hx.trans hy.symm
  exact (J.isPathConnected_space_of_connected_edgeGraph hgraph).isConnected

/-- Actual surface incidence and the two marked incident edges construct
the rim arcs and prove the cut component's marked-vertex link connected. -/
theorem markedTriangleComponent_link_isConnected_at_marked_vertex
    (A L : SimplicialComplex ℝ E) [Fintype A.faces] [Fintype L.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (C : (A.markedTriangleGraph L).ConnectedComponent)
    {v a b : E} (hvC : v ∈ (A.markedTriangleComponent L C).vertices)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v, a} ∈ L.faces) (hb : {v, b} ∈ L.faces)
    (hlink : IsConnected (A.link v).space)
    (hmarked : ∀ s ∈ L.faces, v ∈ s → s.card = 2 → s = {v, a} ∨ s = {v, b}) :
    IsConnected ((A.markedTriangleComponent L C).link v).space := by
  classical
  let edge : Bool → Finset E := fun j ↦ if j then {v, b} else {v, a}
  have hedge (j : Bool) : edge j ∈ L.faces := by cases j; exact ha; exact hb
  have hcard (j : Bool) : (edge j).card = 2 := by
    cases j
    · exact Finset.card_pair hva
    · exact Finset.card_pair hvb
  have hv (j : Bool) : v ∈ edge j := by cases j <;> simp [edge]
  have hne : edge false ≠ edge true := by
    intro h
    have hmem : a ∈ edge true := h ▸ (show a ∈ edge false by simp [edge])
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hva h.symm
    · exact hab (Finset.mem_singleton.mp h)
  have hvL : v ∈ L.vertices := L.down_closed ha (by simp) (by simp)
  obtain ⟨_, _, _, _, _, U₀, U₁, _, _, hU₀, hU₁, hcover, hinter, _⟩ :=
    exists_boundary_circle_vertex_cut A L hLA hpure hcofaces hLcard hvL hlink
      edge hedge hcard hv hne hmarked
  let arc : Bool → Set E := fun j ↦ if j then U₁ else U₀
  have hArc (j : Bool) : IsFinitePLBallPair ℝ (arc j)
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id} := by
    cases j
    · exact hU₀
    · exact hU₁
  exact A.markedTriangleComponent_link_isConnected_of_rim_arcs L C hvC hva hvb hab
    (hLA ha) (hLA hb) hmarked arc hArc hcover hinter

end Geometry.SimplicialComplex
