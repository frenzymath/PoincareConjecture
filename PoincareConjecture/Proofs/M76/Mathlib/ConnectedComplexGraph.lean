import PoincareConjecture.Proofs.M76.Mathlib.ComplexCycleLabels
import PoincareConjecture.Proofs.M76.Mathlib.VertexAbstractComplex
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

omit [DecidableEq E] in

theorem finite_vertices_of_finite_faces (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) : K.vertices.Finite :=
  hfinite.preimage Finset.singleton_injective.injOn

theorem reachable_vertices_of_mem_face (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (u v : K.vertices)
    (hu : u.val ∈ s) (hv : v.val ∈ s) :
    K.vertexAbstractComplex.edgeGraph.Reachable u v := by
  by_cases huv : u = v
  · exact huv ▸ SimpleGraph.Reachable.refl u
  · apply SimpleGraph.Adj.reachable
    refine ⟨huv, ?_⟩
    change ({u, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
    simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
    exact K.down_closed hs (by simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hu hv) (Finset.insert_nonempty _ _)

variable [FiniteDimensional ℝ E]

theorem preconnected_edgeGraph_of_isPreconnected (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (hc : IsPreconnected K.space) :
    K.vertexAbstractComplex.edgeGraph.Preconnected := by
  classical
  intro u v
  let G := K.vertexAbstractComplex.edgeGraph
  let r : E → ℝ := fun x => if hx : x ∈ K.vertices then
    if G.Reachable u ⟨x, hx⟩ then 0 else 1 else 0
  have hr (x : K.vertices) : r x = if G.Reachable u x then 0 else 1 := by
    simp only [r, dif_pos x.property]
  have hrrange : ∀ x, r x ∈ ({0, 1} : Set ℝ) := by
    intro x
    dsimp only [r]
    split_ifs <;> simp
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices r
  have hfrange : MapsTo f K.space ({0, 1} : Set ℝ) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces hs
    have hsvertices : (s : Set E) ⊆ K.vertices := by
      rw [vertices_eq]
      exact subset_biUnion_of_mem hs
    let a' : K.vertices := ⟨a, hsvertices ha⟩
    obtain ⟨b, hb⟩ := hf s hs
    have heq : EqOn b.toAffineMap (AffineMap.const ℝ E (r a)) (s : Set E) := by
      intro y hy
      let y' : K.vertices := ⟨y, hsvertices hy⟩
      have hya : G.Reachable y' a' := K.reachable_vertices_of_mem_face hs y' a' hy ha
      have hre : G.Reachable u y' ↔ G.Reachable u a' :=
        ⟨fun h => h.trans hya, fun h => h.trans hya.symm⟩
      have hray : r y = r a := by
        change r y' = r a'
        rw [hr, hr, hre]
      exact (hb (subset_convexHull ℝ _ hy)).symm.trans ((hfv (hsvertices hy)).trans hray)
    have hfx : f x = r a := (hb hxs).trans
      (AffineMap.eqOn_affineSpan heq (convexHull_subset_affineSpan _ hxs))
    rw [hfx]
    exact hrrange a
  have hconst : f u = f v := hc.constant_of_mapsTo ((finite_singleton (1 : ℝ)).insert 0).isDiscrete
    (hf.continuousOn hfinite) hfrange
      (vertices_subset_space u.property) (vertices_subset_space v.property)
  rw [hfv u.property, hfv v.property, hr, hr,
    if_pos (SimpleGraph.Reachable.refl u)] at hconst
  by_contra hnot
  rw [if_neg hnot] at hconst
  exact zero_ne_one hconst

theorem connected_edgeGraph_of_isConnected (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (hc : IsConnected K.space) :
    K.vertexAbstractComplex.edgeGraph.Connected := by
  obtain ⟨x, hx⟩ := hc.1
  obtain ⟨s, hs, _⟩ := mem_space_iff.mp hx
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvK : v ∈ K.vertices := by
    rw [vertices_eq]
    exact mem_iUnion₂.mpr ⟨s, hs, hv⟩
  let : Nonempty K.vertices := ⟨⟨v, hvK⟩⟩
  exact ⟨K.preconnected_edgeGraph_of_isPreconnected hfinite hc.2⟩

end Geometry.SimplicialComplex
