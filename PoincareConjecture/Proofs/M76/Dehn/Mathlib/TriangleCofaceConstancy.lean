import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCochainIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)

theorem triangle_coface_constancy_of_link
    (a : Triangle K.toPreAbstractSimplicialComplex → Y)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    {s : Finset E} (hcard : s.card < 3)
    (hconn : (K.faceLink s).vertexAbstractComplex.edgeGraph.Preconnected)
    (hnext : ∀ v : (K.faceLink s).vertices,
      ∀ q r : Triangle K.toPreAbstractSimplicialComplex,
        insert (v : E) s ⊆ q.val → insert (v : E) s ⊆ r.val → a q = a r)
    (q r : Triangle K.toPreAbstractSimplicialComplex)
    (hsq : s ⊆ q.val) (hsr : s ⊆ r.val) : a q = a r := by
  classical
  have hcoface (v : (K.faceLink s).vertices) :
      ∃ c : Triangle K.toPreAbstractSimplicialComplex,
        insert (v : E) s ⊆ c.val := by
    have hv : insert (v : E) s ∈ K.faces := by
      simpa only [Finset.union_singleton] using v.property.2.2
    obtain ⟨t, ht, hvt, htc⟩ := hpure _ hv
    exact ⟨⟨t, ht, htc⟩, hvt⟩
  choose c hc using hcoface
  have hedge {u v : (K.faceLink s).vertices}
      (huv : (K.faceLink s).vertexAbstractComplex.edgeGraph.Adj u v) :
      a (c u) = a (c v) := by
    have huvface : ({(u : E), (v : E)} : Finset E) ∈ (K.faceLink s).faces := by
      have hmap := huv.2
      change ({u, v} : Finset (K.faceLink s).vertices).map
        (Function.Embedding.subtype _) ∈ (K.faceLink s).faces at hmap
      simpa only [Finset.map_insert, Finset.map_singleton,
        Function.Embedding.coe_subtype] using hmap
    obtain ⟨t, ht, hst, htc⟩ := hpure _ huvface.2.2
    let d : Triangle K.toPreAbstractSimplicialComplex := ⟨t, ht, htc⟩
    have hu : insert (u : E) s ⊆ d.val := Finset.insert_subset_iff.mpr
      ⟨hst (Finset.mem_union_right _ (Finset.mem_insert_self _ _)),
        (Finset.subset_union_left : s ⊆ s ∪ {(u : E), (v : E)}).trans hst⟩
    have hv : insert (v : E) s ⊆ d.val := Finset.insert_subset_iff.mpr
      ⟨hst (Finset.mem_union_right _ (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))),
        (Finset.subset_union_left : s ⊆ s ∪ {(u : E), (v : E)}).trans hst⟩
    exact (hnext u (c u) d (hc u) hu).trans (hnext v d (c v) hv (hc v))
  have hconstant (u v : (K.faceLink s).vertices) : a (c u) = a (c v) := by
    obtain ⟨p⟩ := hconn u v
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hedge h).trans ih
  have hvertex (t : Triangle K.toPreAbstractSimplicialComplex) (hst : s ⊆ t.val) :
      ∃ v : (K.faceLink s).vertices, insert (v : E) s ⊆ t.val := by
    obtain ⟨v, hvt, hvs⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show s.card < t.val.card by rw [t.property.2]; exact hcard)
    have hvlink : v ∈ (K.faceLink s).vertices := by
      refine ⟨K.down_closed t.property.1 (Finset.singleton_subset_iff.mpr hvt)
        (Finset.singleton_nonempty v), Finset.disjoint_singleton_right.mpr hvs, ?_⟩
      exact K.down_closed t.property.1
        (Finset.union_subset hst (Finset.singleton_subset_iff.mpr hvt))
        (Finset.union_nonempty.mpr (Or.inr (Finset.singleton_nonempty v)))
    exact ⟨⟨v, hvlink⟩, Finset.insert_subset_iff.mpr ⟨hvt, hst⟩⟩
  obtain ⟨u, hu⟩ := hvertex q hsq
  obtain ⟨v, hv⟩ := hvertex r hsr
  exact (hnext u q (c u) hu (hc u)).trans
    ((hconstant u v).trans (hnext v (c v) r (hc v) hv))

theorem triangle_label_constant
    (a : Triangle K.toPreAbstractSimplicialComplex → Y)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hconn : K.vertexAbstractComplex.edgeGraph.Preconnected)
    (hlinks : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected)
    (hedge : ∀ t ∈ K.faces, t.card = 2 →
      ∀ q r : Triangle K.toPreAbstractSimplicialComplex,
        t ⊆ q.val → t ⊆ r.val → a q = a r)
    (q r : Triangle K.toPreAbstractSimplicialComplex) : a q = a r := by
  classical
  have hsingleton (v : K.vertices)
      (q r : Triangle K.toPreAbstractSimplicialComplex)
      (hvq : (v : E) ∈ q.val) (hvr : (v : E) ∈ r.val) : a q = a r := by
    apply K.triangle_coface_constancy_of_link a hpure
      (s := {(v : E)}) (by simp) (hlinks _ v.property) _ q r
      (Finset.singleton_subset_iff.mpr hvq) (Finset.singleton_subset_iff.mpr hvr)
    intro w u z hwu hwz
    have hwface : insert (w : E) {(v : E)} ∈ K.faces := by
      simpa only [Finset.union_singleton] using w.property.2.2
    have hwc : (insert (w : E) {(v : E)} : Finset E).card = 2 := by
      rw [Finset.card_insert_of_notMem
        (K.faceLink_vertices_subset {(v : E)} w.property).2, Finset.card_singleton]
    exact hedge _ hwface hwc u z hwu hwz
  have hcoface (v : K.vertices) :
      ∃ c : Triangle K.toPreAbstractSimplicialComplex, (v : E) ∈ c.val := by
    obtain ⟨t, ht, hvt, htc⟩ := hpure _ v.property
    exact ⟨⟨t, ht, htc⟩, hvt (Finset.mem_singleton_self _)⟩
  choose c hc using hcoface
  have hadj {u v : K.vertices} (huv : K.vertexAbstractComplex.edgeGraph.Adj u v) :
      a (c u) = a (c v) := by
    have huvface : ({(u : E), (v : E)} : Finset E) ∈ K.faces := by
      have hmap := huv.2
      change ({u, v} : Finset K.vertices).map
        (Function.Embedding.subtype _) ∈ K.faces at hmap
      simpa only [Finset.map_insert, Finset.map_singleton,
        Function.Embedding.coe_subtype] using hmap
    obtain ⟨t, ht, hvt, htc⟩ := hpure _ huvface
    let d : Triangle K.toPreAbstractSimplicialComplex := ⟨t, ht, htc⟩
    have hu : (u : E) ∈ d.val := hvt (Finset.mem_insert_self _ _)
    have hv : (v : E) ∈ d.val := hvt (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact (hsingleton u (c u) d (hc u) hu).trans
      (hsingleton v d (c v) hv (hc v))
  have hconstant (u v : K.vertices) : a (c u) = a (c v) := by
    obtain ⟨p⟩ := hconn u v
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj h).trans ih
  obtain ⟨u, hu⟩ := K.nonempty_of_mem_faces q.property.1
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces r.property.1
  have huK : u ∈ K.vertices := K.down_closed q.property.1
    (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty u)
  have hvK : v ∈ K.vertices := K.down_closed r.property.1
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  exact (hsingleton ⟨u, huK⟩ q (c ⟨u, huK⟩) hu (hc _)).trans
    ((hconstant ⟨u, huK⟩ ⟨v, hvK⟩).trans
      (hsingleton ⟨v, hvK⟩ (c ⟨v, hvK⟩) r (hc _) hv))

end Geometry.SimplicialComplex
