import PoincareConjecture.Proofs.M76.Mathlib.GeometricPathIntervals
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem isFinitePLBallPair_of_pure_edges_with_leaf
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 2 ∧ s ⊆ t)
    (hconn : K.vertexAbstractComplex.edgeGraph.Connected)
    (hdegree : ∀ v, (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2)
    (hleaf : ∃ v, (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) :
    IsFinitePLBallPair ℝ K.space
      (Subtype.val '' {v : K.vertices |
        (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1}) := by
  classical
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let G := K.vertexAbstractComplex.edgeGraph
  have hedge {v w : K.vertices} (hvw : G.Adj v w) :
      ({(v : E), (w : E)} : Finset E) ∈ K.faces := by
    have h := hvw.2
    change ({v, w} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      using h
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
      obtain ⟨v, w, hvw, htval⟩ := Finset.card_eq_two.mp htc
      subst t
      have hv : v ∈ K.vertices := K.down_closed ht
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
        (Finset.singleton_nonempty v)
      have hw : w ∈ K.vertices := K.down_closed ht
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        (Finset.singleton_nonempty w)
      have hadj : G.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
        refine ⟨fun h => hvw (congrArg Subtype.val h), ?_⟩
        change ({(⟨v, hv⟩ : K.vertices), ⟨w, hw⟩} : Finset K.vertices).map
          (Function.Embedding.subtype _) ∈ K.faces
        simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
          using ht
      refine ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj, ?_⟩
      simpa only [Finset.coe_pair, convexHull_pair] using convexHull_mono hst hxs
  have hball := G.isFinitePLBallPair_segmentCarrier_of_leaf
    ((↑) : K.vertices → E) hconn hdegree hleaf Subtype.val_injective
    (fun {_ _ _ _} hvw hab => hinter hvw hab)
  rwa [hcarrier] at hball

end Geometry.SimplicialComplex
