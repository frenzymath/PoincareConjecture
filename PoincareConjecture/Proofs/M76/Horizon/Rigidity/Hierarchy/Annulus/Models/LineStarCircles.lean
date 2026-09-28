import PoincareConjecture.Proofs.M76.Mathlib.PureEdgeComplexPolygon
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedManifoldConditions
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks

set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem pure_edges_and_degree_two_of_real_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hstars : ∀ p ∈ K.vertices, ∃ (a : E → ℝ),
      (K.closedStar p).AffineOnFaces a ∧ InjOn a (K.closedStar p).space ∧
      a p ∈ interior (a '' (K.closedStar p).space)) :
    (∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 2 ∧ s ⊆ t) ∧
      ∀ v, (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
  classical
  have hbound : ∀ s ∈ K.faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
    obtain ⟨a, hf, hi, _⟩ := hstars p (K.face_subset_vertices hs hps)
    have hsS : s ∈ (K.closedStar p).faces :=
      ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
    have hsJ := (hf.image_mem_embeddedImage_iff hi
      ((K.closedStar p).subset_space hsS)).mpr hsS
    have hb := ((hf.embeddedImage hi).indep hsJ).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simp only [Fintype.card_coe] at hb
    rw [Finset.card_image_iff.mpr (hi.mono ((K.closedStar p).subset_space hsS))] at hb
    simpa using hb
  have hdegree : ∀ v, (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
    intro v
    obtain ⟨a, hf, hi, hint⟩ := hstars v v.property
    let S := K.closedStar (v : E)
    have hvface : {(v : E)} ∈ K.faces := v.property
    have hvS : {(v : E)} ∈ S.faces :=
      ⟨hvface, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using hvface⟩
    let J := hf.embeddedImage hi
    have hJ : J.faces.Finite := hf.embeddedImage_finite hi (finite_closedStar_faces hK v)
    have hvJ : ({(v : E)} : Finset E).image a ∈ J.faces :=
      (hf.image_mem_embeddedImage_iff hi (S.subset_space hvS)).mpr hvS
    have hc := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hvJ (by simp)
      ⟨a v, by simp, by simpa only [J, hf.embeddedImage_space hi] using hint⟩
    rw [hf.ncard_embeddedImage_faceLink hi hvS] at hc
    have hSl : S.faceLink {(v : E)} = K.faceLink {(v : E)} := by
      rw [show S = K.closedFaceStar {(v : E)} from
        (K.closedFaceStar_singleton_eq_closedStar v).symm]
      exact K.closedFaceStar_faceLink_of_subset (Finset.Subset.refl _)
    rw [hSl] at hc
    exact (K.ncard_edgeGraph_neighborSet v).trans hc
  refine ⟨?_, hdegree⟩
  intro s hs
  have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hle := hbound s hs
  by_cases hc : s.card = 2
  · exact ⟨s, hs, hc, Finset.Subset.refl _⟩
  have hc1 : s.card = 1 := by omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc1
  have hn := hdegree ⟨v, hs⟩
  obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    (K.vertexAbstractComplex.edgeGraph.neighborSet ⟨v, hs⟩).ncard ≠ 0)
  have hedge : ({v, (w : E)} : Finset E) ∈ K.faces := by
    have hh := hw.2
    change ({(⟨v, hs⟩ : K.vertices), w} : Finset K.vertices).map
      (Function.Embedding.subtype _) ∈ K.faces at hh
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hh
  exact ⟨{v, (w : E)}, hedge,
    Finset.card_pair (fun he => hw.1 (Subtype.ext he)), by simp⟩

theorem hasDisjointPolygonPresentation_of_real_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hstars : ∀ p ∈ K.vertices, ∃ (a : E → ℝ),
      (K.closedStar p).AffineOnFaces a ∧ InjOn a (K.closedStar p).space ∧
      a p ∈ interior (a '' (K.closedStar p).space)) :
    HasDisjointPolygonPresentation K.space := by
  classical
  obtain ⟨hpure, hdegree⟩ := K.pure_edges_and_degree_two_of_real_stars hK hstars
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let G := K.vertexAbstractComplex.edgeGraph
  have hedge {v w : K.vertices} (hvw : G.Adj v w) :
      ({(v : E), (w : E)} : Finset E) ∈ K.faces := by
    have h := hvw.2
    change ({v, w} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using h
  have hinter {v w a b : K.vertices} (hvw : G.Adj v w) (hab : G.Adj a b) :
      segment ℝ (v : E) (w : E) ∩ segment ℝ (a : E) (b : E) ⊆
        convexHull ℝ (({(v : E), (w : E)} : Set E) ∩ {(a : E), (b : E)}) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      K.inter_subset_convexHull (hedge hvw) (hedge hab)
  have hcarrier : G.segmentCarrier ((↑) : K.vertices → E) = K.space := by
    apply Subset.antisymm
    · rintro x ⟨v, w, hvw, hx⟩
      apply K.convexHull_subset_space (hedge hvw)
      simpa only [Finset.coe_pair, convexHull_pair] using hx
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      obtain ⟨t, ht, htc, hst⟩ := hpure s hs
      obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp htc
      have hv := K.face_subset_vertices ht (Finset.mem_insert_self v {w})
      have hw := K.face_subset_vertices ht (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
      have hadj : G.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
        refine ⟨fun h => hvw (congrArg Subtype.val h), ?_⟩
        change ({(⟨v, hv⟩ : K.vertices), ⟨w, hw⟩} : Finset K.vertices).map
          (Function.Embedding.subtype _) ∈ K.faces
        simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using ht
      refine ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj, ?_⟩
      simpa only [Finset.coe_pair, convexHull_pair] using convexHull_mono hst hxs
  obtain ⟨n, P, hP, hcover, hdis⟩ := G.exists_component_polygons_of_two_neighbors
    ((↑) : K.vertices → E) hdegree Subtype.val_injective
    (fun {_ _ _ _} hvw hab => hinter hvw hab)
  exact hasDisjointPolygonPresentation_of_family n P
    (fun i => ⟨(hP i).1, (hP i).2.1⟩) (hcarrier.symm.trans hcover) hdis

end Geometry.SimplicialComplex
