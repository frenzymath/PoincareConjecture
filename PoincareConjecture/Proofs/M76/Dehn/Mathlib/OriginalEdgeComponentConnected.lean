import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponent
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseLinkSection










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)



def edgeComponentVertexEquiv (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    (K.edgeComponentComplex C).vertices ≃ C where
  toFun p :=
    ⟨⟨p.val, K.edgeComponentComplex_le C p.property⟩,
      (K.edgeComponentComplex_vertex_iff C
        ⟨p.val, K.edgeComponentComplex_le C p.property⟩).mp p.property⟩
  invFun p := ⟨p.val.val, (K.edgeComponentComplex_vertex_iff C p.val).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl




def edgeComponentGraphHom (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    C.toSimpleGraph →g (K.edgeComponentComplex C).vertexAbstractComplex.edgeGraph where
  toFun := (K.edgeComponentVertexEquiv C).symm
  map_rel' := by
    intro p q hpq
    refine ⟨?_, ?_⟩
    · intro heq
      exact hpq.1 (congrArg Subtype.val ((K.edgeComponentVertexEquiv C).symm.injective heq))
    · change ({(K.edgeComponentVertexEquiv C).symm p,
          (K.edgeComponentVertexEquiv C).symm q} :
          Finset (K.edgeComponentComplex C).vertices).map
        (Function.Embedding.subtype _) ∈ (K.edgeComponentComplex C).faces
      simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      change ({p.val.val, q.val.val} : Finset E) ∈ (K.edgeComponentComplex C).faces
      have hface := hpq.2
      change ({p.val, q.val} : Finset K.vertices).map
        (Function.Embedding.subtype _) ∈ K.faces at hface
      simp only [Finset.map_insert, Finset.map_singleton,
        Function.Embedding.coe_subtype] at hface
      exact K.edgeComponentComplex_coface C
        ((K.edgeComponentComplex_vertex_iff C p.val).mpr p.property) hface
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))



theorem edgeComponentComplex_connected
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    (K.edgeComponentComplex C).vertexAbstractComplex.edgeGraph.Connected :=
  SimpleGraph.Connected.map (K.edgeComponentGraphHom C)
    (K.edgeComponentVertexEquiv C).symm.surjective C.connected_toSimpleGraph



theorem edgeComponentComplex_isPathConnected
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    IsPathConnected (K.edgeComponentComplex C).space :=
  (K.edgeComponentComplex C).isPathConnected_space_of_connected_edgeGraph
    (K.edgeComponentComplex_connected C)

end Geometry.SimplicialComplex
