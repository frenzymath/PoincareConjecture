import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence
import PoincareConjecture.Proofs.M76.Smoothing.CyclicFacePlanes










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem contractible_faceStarPlanes_of_link_incidence (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hc : IsConnected (K.faceLink s).space)
    (hdim : ∀ t ∈ (K.faceLink s).faces, t.card ≤ 2)
    (hlinks : ∀ u : (K.faceLink s).vertices,
      (K.faceLink (s ∪ {u.val})).vertices.ncard = 2) :
    ContractibleSpace (SecantTransversePlaneSpace
      (2 + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction)
      (K.closedFaceStar s).space) := by
  let L := K.faceLink s
  have hL : L.faces.Finite := SimplicialComplex.finite_faceLink_faces hfinite s
  let : Finite L.vertices := (L.finite_vertices_of_finite_faces hL).to_subtype
  have hdim' : ∀ t ∈ L.vertexAbstractComplex.faces, t.card ≤ 2 := by
    intro t ht
    simpa only [Finset.card_map] using hdim (t.map (Function.Embedding.subtype _)) ht
  have hdegree : ∀ u, (L.vertexAbstractComplex.edgeGraph.neighborSet u).ncard = 2 := by
    intro u
    rw [K.ncard_faceLink_edgeGraph_neighborSet s u]
    exact hlinks u
  obtain ⟨n, e, he⟩ := L.vertexAbstractComplex.exists_cyclic_face_labels hdim'
    (L.connected_edgeGraph_of_isConnected hL hc) hdegree
  exact contractible_cyclicFaceStarPlanes K hK hs e (fun t => (he t).symm)

end PoincareConjecture.M76.Smoothing
