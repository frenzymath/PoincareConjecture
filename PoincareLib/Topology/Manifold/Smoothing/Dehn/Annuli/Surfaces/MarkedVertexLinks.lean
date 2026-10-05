import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surfaces.MarkedTriangleComponents
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.TriangleCofaceConstancy
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkCofaceCount

/-!
# Whole vertex links away from the marked circles

Deleting the marked triangle adjacencies leaves every other vertex star
unchanged in its selected component. This is derived from walks in the
original vertex link, not assumed as local manifold data of the cut.
-/

set_option autoImplicit false
open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K L : SimplicialComplex ℝ E)

/-- At an unmarked vertex, membership of an original triangular coface
is constant in each actual component of the cut triangle graph. -/
theorem markedTriangleComponent_cofaces_at_unmarked_vertex
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {v : E} (hv : v ∉ L.vertices) (hlink : IsConnected (K.link v).space)
    (q r : Triangle K.toPreAbstractSimplicialComplex)
    (hvq : v ∈ q.val) (hvr : v ∈ r.val) :
    q.val ∈ (K.markedTriangleComponent L C).faces ↔
      r.val ∈ (K.markedTriangleComponent L C).faces := by
  have hconn : (K.faceLink {v}).vertexAbstractComplex.edgeGraph.Preconnected := by
    rw [K.faceLink_singleton_eq_link]
    exact ((K.link v).connected_edgeGraph_of_isConnected (finite_link_faces hK v)
      hlink).preconnected
  apply of_eq
  apply K.triangle_coface_constancy_of_link
    (fun t ↦ t.val ∈ (K.markedTriangleComponent L C).faces)
    (fun s hs ↦ by
      obtain ⟨t, ht, htc, hst⟩ := hpure s hs
      exact ⟨t, ht, hst, htc⟩)
    (s := {v}) (by simp) hconn _ q r
    (Finset.singleton_subset_iff.mpr hvq) (Finset.singleton_subset_iff.mpr hvr)
  intro w t u hwt hwu
  have hcard : (insert (w : E) {v} : Finset E).card = 2 := by
    rw [Finset.card_insert_of_notMem
      (K.faceLink_vertices_subset {v} w.property).2, Finset.card_singleton]
  have hmark : (insert (w : E) {v} : Finset E) ∉ L.faces := by
    intro hs
    exact hv (L.down_closed hs (by simp) (Finset.singleton_nonempty v))
  apply propext
  constructor
  · intro ht
    exact K.markedTriangleComponent_unmarked_coface L C
      ((K.markedTriangleComponent L C).down_closed ht hwt (by simp))
      hcard hmark u.property.1 u.property.2 hwu
  · intro hu
    exact K.markedTriangleComponent_unmarked_coface L C
      ((K.markedTriangleComponent L C).down_closed hu hwu (by simp))
      hcard hmark t.property.1 t.property.2 hwt

/-- The full original link is retained at every unmarked vertex of the
actual selected component. -/
theorem markedTriangleComponent_link_at_unmarked_vertex
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {v : E} (hvC : v ∈ (K.markedTriangleComponent L C).vertices)
    (hv : v ∉ L.vertices) (hlink : IsConnected (K.link v).space) :
    (K.markedTriangleComponent L C).link v = K.link v := by
  obtain ⟨q, hq, hqc, hvq⟩ := K.markedTriangleComponent_pure L C {v} hvC
  let q' : Triangle K.toPreAbstractSimplicialComplex := ⟨q, hq.1, hqc⟩
  apply SimplicialComplex.ext
  ext s
  constructor
  · exact fun hs ↦ ⟨hs.1.1, hs.2.1, hs.2.2.1⟩
  · intro hs
    obtain ⟨t, ht, htc, hst⟩ := hpure (insert v s) hs.2.2
    let t' : Triangle K.toPreAbstractSimplicialComplex := ⟨t, ht, htc⟩
    have htC : t ∈ (K.markedTriangleComponent L C).faces :=
      (K.markedTriangleComponent_cofaces_at_unmarked_vertex L hK hpure C hv hlink q' t'
        (hvq (Finset.mem_singleton_self v)) (hst (Finset.mem_insert_self v s))).mp hq
    exact ⟨(K.markedTriangleComponent L C).down_closed htC
        ((Finset.subset_insert v s).trans hst) (K.nonempty_of_mem_faces hs.1), hs.2.1,
      (K.markedTriangleComponent L C).down_closed htC hst (Finset.insert_nonempty v s)⟩

theorem markedTriangleComponent_link_isConnected_at_unmarked_vertex
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {v : E} (hvC : v ∈ (K.markedTriangleComponent L C).vertices)
    (hv : v ∉ L.vertices) (hlink : IsConnected (K.link v).space) :
    IsConnected ((K.markedTriangleComponent L C).link v).space := by
  rw [K.markedTriangleComponent_link_at_unmarked_vertex L hK hpure C hvC hv hlink]
  exact hlink

end Geometry.SimplicialComplex
