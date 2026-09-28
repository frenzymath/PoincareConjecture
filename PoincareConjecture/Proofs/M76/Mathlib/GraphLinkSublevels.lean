import PoincareConjecture.Proofs.M76.Mathlib.GraphHeightSublevels
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem lower_neighbors_reachable_of_preconnected_link
    (K : SimplicialComplex ℝ E) (A : E → ℝ) (p : K.vertices)
    (hlink : ((K.link (p : E)).vertexAbstractComplex.edgeGraph.induce
      {v : (K.link (p : E)).vertices | A (v : E) < A p}).Preconnected)
    (a b : K.vertices) (hpa : K.vertexAbstractComplex.edgeGraph.Adj p a)
    (hpb : K.vertexAbstractComplex.edgeGraph.Adj p b)
    (ha : A a < A p) (hb : A b < A p) :
    (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | A (v : E) < A p}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hneighbor (v : K.vertices) (hpv : K.vertexAbstractComplex.edgeGraph.Adj p v) :
      (v : E) ∈ (K.link (p : E)).vertices := by
    refine ⟨v.property, ?_, ?_⟩
    · intro h
      exact hpv.1 (Subtype.ext (Finset.mem_singleton.mp h))
    · have hface := hpv.2
      change ({p, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
        at hface
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
        using hface
  let lift : (K.link (p : E)).vertexAbstractComplex.edgeGraph.induce
      {v : (K.link (p : E)).vertices | A (v : E) < A p} →g
      K.vertexAbstractComplex.edgeGraph.induce {v : K.vertices | A (v : E) < A p} :=
    { toFun := fun x => ⟨⟨x.val, x.val.property.1⟩, x.property⟩
      map_rel' := by
        intro x y hxy
        refine ⟨?_, ?_⟩
        · intro h
          have hval : (x.val : E) = (y.val : E) :=
            congrArg (fun z : K.vertices => (z : E)) h
          exact hxy.1 (Subtype.ext hval)
        · have hface := hxy.2
          change ({x.val, y.val} : Finset (K.link (p : E)).vertices).map
            (Function.Embedding.subtype _) ∈ (K.link (p : E)).faces at hface
          change ({(⟨x.val, x.val.property.1⟩ : K.vertices),
            (⟨y.val, y.val.property.1⟩ : K.vertices)} : Finset K.vertices).map
            (Function.Embedding.subtype _) ∈ K.faces
          simp only [Finset.map_insert, Finset.map_singleton,
            Function.Embedding.coe_subtype] at hface ⊢
          exact hface.1 }
  exact (hlink ⟨⟨a, hneighbor a hpa⟩, ha⟩ ⟨⟨b, hneighbor b hpb⟩, hb⟩).map lift

theorem preconnected_sublevel_graph_of_preconnected_links
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hG : K.vertexAbstractComplex.edgeGraph.Preconnected)
    (A : E → ℝ) (hA : InjOn A K.vertices)
    (hlink : ∀ p ∈ K.vertices,
      ((K.link p).vertexAbstractComplex.edgeGraph.induce
        {v : (K.link p).vertices | A (v : E) < A p}).Preconnected)
    (c : ℝ) : (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | A (v : E) < c}).Preconnected := by
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  apply hG.induce_lt_of_lower_neighbors (fun v : K.vertices => A v)
    (fun x y h => Subtype.ext (hA x.property y.property h)) ?_ c
  intro p a b hpa hpb ha hb
  exact K.lower_neighbors_reachable_of_preconnected_link A p (hlink p p.property)
    a b hpa hpb ha hb

theorem preconnected_signed_sublevel_graphs_of_preconnected_links
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hG : K.vertexAbstractComplex.edgeGraph.Preconnected)
    (A : E → ℝ) (hA : InjOn A K.vertices)
    (hlink : ∀ p ∈ K.vertices,
      ((K.link p).vertexAbstractComplex.edgeGraph.induce
        {v : (K.link p).vertices | A (v : E) < A p}).Preconnected ∧
        ((K.link p).vertexAbstractComplex.edgeGraph.induce
          {v : (K.link p).vertices | A p < A (v : E)}).Preconnected)
    (c : ℝ) :
    (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | A (v : E) < c}).Preconnected ∧
      (K.vertexAbstractComplex.edgeGraph.induce
        {v : K.vertices | c < A (v : E)}).Preconnected := by
  refine ⟨K.preconnected_sublevel_graph_of_preconnected_links hK hG A hA
    (fun p hp => (hlink p hp).1) c, ?_⟩
  have hnegA : InjOn (fun x => -A x) K.vertices := by
    intro x hx y hy h
    exact hA hx hy (neg_injective h)
  have hnegLink : ∀ p ∈ K.vertices,
      ((K.link p).vertexAbstractComplex.edgeGraph.induce
        {v : (K.link p).vertices | -A (v : E) < -A p}).Preconnected := by
    intro p hp
    have hs : {v : (K.link p).vertices | -A (v : E) < -A p} =
        {v : (K.link p).vertices | A p < A (v : E)} := by
      ext v
      change (-A (v : E) < -A p) ↔ A p < A (v : E)
      exact neg_lt_neg_iff
    exact hs.symm ▸ (hlink p hp).2
  have h := K.preconnected_sublevel_graph_of_preconnected_links hK hG
    (fun x => -A x) hnegA hnegLink (-c)
  have hs : {v : K.vertices | -A (v : E) < -c} =
      {v : K.vertices | c < A (v : E)} := by
    ext v
    change (-A (v : E) < -c) ↔ c < A (v : E)
    exact neg_lt_neg_iff
  exact hs ▸ h

end Geometry.SimplicialComplex
