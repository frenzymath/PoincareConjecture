import PoincareConjecture.Proofs.M76.Mathlib.VertexZeroChargeSignedLinks
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSignPerturbation
import PoincareConjecture.Proofs.M76.Mathlib.FiniteGenericHeightTilt











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem preconnected_signed_vertex_link_graphs_of_zero_charge
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {p : E} (hp : p ∈ K.vertices) (hconn : IsConnected (K.link p).space)
    (A : E →ᵃ[ℝ] ℝ)
    (hpres : HasAlexanderCurvePresentation (K.space ∩ {x | A x = A p}) 0)
    (hsigns : p ∈ closure ((K.space ∩ {x | A x = A p}) \ {p}) →
      p ∈ closure (K.space ∩ {x | A x < A p}) ∧
        p ∈ closure (K.space ∩ {x | A p < A x}))
    (f : E → ℝ)
    (horder : ∀ x ∈ K.vertices, ∀ y ∈ K.vertices, A x < A y → f x < f y) :
    ((K.link p).vertexAbstractComplex.edgeGraph.induce
      {v : (K.link p).vertices | f (v : E) < f p}).Preconnected ∧
      ((K.link p).vertexAbstractComplex.edgeGraph.induce
        {v : (K.link p).vertices | f p < f (v : E)}).Preconnected := by
  obtain ⟨hn, hpos, hz⟩ :=
    K.zero_charge_vertex_link_sign_data hK hpure hcofaces hp hconn A hpres hsigns
  have hlink := finite_link_faces hK p
  have hpgraph := (K.link p).preconnected_positive_vertex_graph_of_sign_preservation
    hlink (A - AffineMap.const ℝ E (A p)) (fun x => f x - f p)
    (by change IsPreconnected ((K.link p).space ∩ {x | 0 < A x - A p})
        simpa only [sub_pos] using hpos)
    (by intro x hx hxA
        change 0 < f x - f p
        exact sub_pos.mpr (horder p hp x hx.1 (sub_pos.mp hxA)))
    (by intro x hx hxA
        change f x - f p < 0
        exact sub_neg.mpr (horder x hx.1 p hp (sub_neg.mp hxA)))
    (by intro x hx hxA
        change x ∈ closure ((K.link p).space ∩ {y | 0 < A y - A p})
        simpa only [sub_pos] using
          (hz x ((K.link p).vertices_subset_space hx) (sub_eq_zero.mp hxA)).2)
  have hngraph := (K.link p).preconnected_positive_vertex_graph_of_sign_preservation
    hlink (AffineMap.const ℝ E (A p) - A) (fun x => f p - f x)
    (by change IsPreconnected ((K.link p).space ∩ {x | 0 < A p - A x})
        simpa only [sub_pos] using hn)
    (by intro x hx hxA
        change 0 < f p - f x
        exact sub_pos.mpr (horder x hx.1 p hp (sub_pos.mp hxA)))
    (by intro x hx hxA
        change f p - f x < 0
        exact sub_neg.mpr (horder p hp x hx.1 (sub_neg.mp hxA)))
    (by intro x hx hxA
        change x ∈ closure ((K.link p).space ∩ {y | 0 < A p - A y})
        simpa only [sub_pos] using
          (hz x ((K.link p).vertices_subset_space hx) (sub_eq_zero.mp hxA).symm).1)
  have hnset : {v : (K.link p).vertices | 0 < f p - f (v : E)} =
      {v : (K.link p).vertices | f (v : E) < f p} := by
    ext v
    change (0 < f p - f (v : E)) ↔ f (v : E) < f p
    exact sub_pos
  have hpset : {v : (K.link p).vertices | 0 < f (v : E) - f p} =
      {v : (K.link p).vertices | f p < f (v : E)} := by
    ext v
    change (0 < f (v : E) - f p) ↔ f p < f (v : E)
    exact sub_pos
  exact ⟨hnset ▸ hngraph, hpset ▸ hpgraph⟩






theorem exists_generic_height_with_preconnected_signed_links
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hconn : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (A : E →ᵃ[ℝ] ℝ)
    (hpres : ∀ c, HasAlexanderCurvePresentation (K.space ∩ {x | A x = c}) 0)
    (hsigns : ∀ p ∈ K.space,
      p ∈ closure ((K.space ∩ {x | A x = A p}) \ {p}) →
        p ∈ closure (K.space ∩ {x | A x < A p}) ∧
          p ∈ closure (K.space ∩ {x | A p < A x})) :
    ∃ B : E →ᵃ[ℝ] ℝ, InjOn B K.vertices ∧
      (∀ x ∈ K.vertices, ∀ y ∈ K.vertices, A x < A y → B x < B y) ∧
      ∀ p ∈ K.vertices,
        ((K.link p).vertexAbstractComplex.edgeGraph.induce
          {v : (K.link p).vertices | B (v : E) < B p}).Preconnected ∧
          ((K.link p).vertexAbstractComplex.edgeGraph.induce
            {v : (K.link p).vertices | B p < B (v : E)}).Preconnected := by
  obtain ⟨L, δ, hδ, _, htilt⟩ :=
    (K.finite_vertices_of_finite_faces hK).exists_generic_affine_height_tilt A
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨hB, horder⟩ := htilt (δ / 2) ⟨half_pos hδ.1, half_lt_self hδ.1⟩
  refine ⟨A + (δ / 2) • L.toAffineMap, hB, horder, ?_⟩
  intro p hp
  exact K.preconnected_signed_vertex_link_graphs_of_zero_charge hK hpure hcofaces hp
    (hconn p hp) A (hpres (A p)) (hsigns p (K.vertices_subset_space hp))
      (A + (δ / 2) • L.toAffineMap) horder

end Geometry.SimplicialComplex
