import PoincareConjecture.Proofs.M76.Mathlib.ConnectedHalfspaceGraph
import Mathlib.Analysis.Convex.PathConnected










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]





theorem isPreconnected_positive_space_of_vertex_graph
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hG : (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | 0 < A (v : E)}).Preconnected) :
    IsPreconnected (K.space ∩ {x | 0 < A x}) := by
  classical
  let V := {v : K.vertices // 0 < A (v : E)}
  let G := K.vertexAbstractComplex.edgeGraph.induce {v : K.vertices | 0 < A (v : E)}
  have hconv : Convex ℝ {x | 0 < A x} := (convex_Ioi (0 : ℝ)).affine_preimage A
  have hedge (u v : V) (h : G.Adj u v) :
      JoinedIn (K.space ∩ {x | 0 < A x}) (u.val : E) (v.val : E) := by
    have he : ({(u.val : E), (v.val : E)} : Finset E) ∈ K.faces := by
      have hface := h.2
      change ({u.val, v.val} : Finset K.vertices).map
        (Function.Embedding.subtype _) ∈ K.faces at hface
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
        using hface
    apply JoinedIn.of_segment_subset
    intro x hx
    refine ⟨?_, hconv.segment_subset u.property v.property hx⟩
    apply K.convexHull_subset_space he
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using hx
  have hwalk (u v : V) (p : G.Walk u v) :
      JoinedIn (K.space ∩ {x | 0 < A x}) (u.val : E) (v.val : E) := by
    induction p with
    | @nil u => exact JoinedIn.refl ⟨K.vertices_subset_space u.val.property, u.property⟩
    | @cons u v w h p ih => exact (hedge u v h).trans ih
  have hanchor (x : E) (hx : x ∈ K.space ∩ {x | 0 < A x}) :
      ∃ v : V, JoinedIn (K.space ∩ {x | 0 < A x}) (v.val : E) x := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
    have hpos : ∃ v ∈ s, 0 < A v := by
      by_contra h
      push Not at h
      have hbound : convexHull ℝ (s : Set E) ⊆ {y | A y ≤ 0} :=
        convexHull_min (fun y hy => h y hy) ((convex_Iic (0 : ℝ)).affine_preimage A)
      exact (show 0 < A x from hx.2).not_ge (hbound hxs)
    obtain ⟨v, hv, hvA⟩ := hpos
    have hvK : v ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    refine ⟨⟨⟨v, hvK⟩, hvA⟩, JoinedIn.of_segment_subset ?_⟩
    intro y hy
    exact ⟨K.convexHull_subset_space hs ((convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ hv) hxs hy), hconv.segment_subset hvA hx.2 hy⟩
  by_cases hne : (K.space ∩ {x | 0 < A x}).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨u, hux⟩ := hanchor x hx
    have hpath : IsPathConnected (K.space ∩ {x | 0 < A x}) := by
      refine ⟨x, hx, ?_⟩
      intro y hy
      obtain ⟨v, hvy⟩ := hanchor y hy
      obtain ⟨p⟩ := hG u v
      exact hux.symm.trans ((hwalk u v p).trans hvy)
    exact hpath.isConnected.isPreconnected
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty




theorem isPreconnected_strict_sides_of_vertex_graphs
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (c : ℝ)
    (hn : (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | A (v : E) < c}).Preconnected)
    (hp : (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | c < A (v : E)}).Preconnected) :
    IsPreconnected (K.space ∩ {x | A x < c}) ∧
      IsPreconnected (K.space ∩ {x | c < A x}) := by
  have hnset : {v : K.vertices | 0 < (AffineMap.const ℝ E c - A) (v : E)} =
      {v : K.vertices | A (v : E) < c} := by
    ext v
    change (0 < c - A (v : E)) ↔ A (v : E) < c
    exact sub_pos
  have hpset : {v : K.vertices | 0 < (A - AffineMap.const ℝ E c) (v : E)} =
      {v : K.vertices | c < A (v : E)} := by
    ext v
    change (0 < A (v : E) - c) ↔ c < A (v : E)
    exact sub_pos
  have hneg := K.isPreconnected_positive_space_of_vertex_graph
    (AffineMap.const ℝ E c - A) (hnset.symm ▸ hn)
  have hpos := K.isPreconnected_positive_space_of_vertex_graph
    (A - AffineMap.const ℝ E c) (hpset.symm ▸ hp)
  change IsPreconnected (K.space ∩ {x | 0 < c - A x}) at hneg
  change IsPreconnected (K.space ∩ {x | 0 < A x - c}) at hpos
  exact ⟨by simpa only [sub_pos] using hneg, by simpa only [sub_pos] using hpos⟩

end Geometry.SimplicialComplex
