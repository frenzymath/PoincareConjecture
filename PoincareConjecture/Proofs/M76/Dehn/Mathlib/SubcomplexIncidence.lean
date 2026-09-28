import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SubcomplexFaceInclusion










set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E)

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex



theorem vertexCoboundary_subcomplex_restrict (hAK : A ≤ K)
    (a : K.vertices → ZMod 2) :
    vertexCoboundary AA (a ∘ K.subcomplexVertexEmbedding A hAK) =
      (vertexCoboundary KA a) ∘ K.subcomplexFaceEmbedding A hAK 2 := by
  classical
  funext e
  change vertexCoboundary AA (a ∘ K.subcomplexVertexEmbedding A hAK) e =
    vertexCoboundary KA a (K.subcomplexFaceEmbedding A hAK 2 e)
  rw [vertexCoboundary_apply, vertexCoboundary_apply,
    K.subcomplexFaceEmbedding_map, Finset.sum_map]
  rfl



theorem boundary1_subcomplex_include (hAK : A ≤ K)
    (c : Module.Dual (ZMod 2) (Edge AA → ZMod 2)) :
    (vertexCoboundary KA).dualMap
        ((LinearMap.funLeft (ZMod 2) (ZMod 2)
          (K.subcomplexFaceEmbedding A hAK 2)).dualMap c) =
      (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (K.subcomplexVertexEmbedding A hAK)).dualMap ((vertexCoboundary AA).dualMap c) := by
  ext a
  change c ((vertexCoboundary KA a) ∘ K.subcomplexFaceEmbedding A hAK 2) =
    c (vertexCoboundary AA (a ∘ K.subcomplexVertexEmbedding A hAK))
  rw [K.vertexCoboundary_subcomplex_restrict A hAK]

variable [Fintype K.vertices] [Fintype A.vertices]

open Classical in


theorem triangleEdges_subcomplex (hAK : A ≤ K) (t : Triangle AA) :
    triangleEdges KA (K.subcomplexFaceEmbedding A hAK 3 t) =
      (triangleEdges AA t).map (K.subcomplexFaceEmbedding A hAK 2) := by
  ext s
  simp only [triangleEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro hst
    obtain ⟨u, ⟨hu, hut⟩, _⟩ := K.exists_unique_subcomplex_lower_face A hAK s t hst
    exact ⟨u, hut, hu⟩
  · rintro ⟨u, hut, rfl⟩
    exact (K.subcomplexFaceEmbedding_subset_iff A hAK u t).mpr hut



theorem edgeCoboundary_subcomplex_restrict (hAK : A ≤ K)
    (z : Edge KA → ZMod 2) :
    edgeCoboundary AA (z ∘ K.subcomplexFaceEmbedding A hAK 2) =
      (edgeCoboundary KA z) ∘ K.subcomplexFaceEmbedding A hAK 3 := by
  classical
  funext t
  change edgeCoboundary AA (z ∘ K.subcomplexFaceEmbedding A hAK 2) t =
    edgeCoboundary KA z (K.subcomplexFaceEmbedding A hAK 3 t)
  rw [edgeCoboundary_apply, edgeCoboundary_apply,
    K.triangleEdges_subcomplex A hAK, Finset.sum_map]
  rfl



theorem boundary2_subcomplex_include (hAK : A ≤ K)
    (c : Module.Dual (ZMod 2) (Triangle AA → ZMod 2)) :
    (edgeCoboundary KA).dualMap
        ((LinearMap.funLeft (ZMod 2) (ZMod 2)
          (K.subcomplexFaceEmbedding A hAK 3)).dualMap c) =
      (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (K.subcomplexFaceEmbedding A hAK 2)).dualMap ((edgeCoboundary AA).dualMap c) := by
  ext z
  change c ((edgeCoboundary KA z) ∘ K.subcomplexFaceEmbedding A hAK 3) =
    c (edgeCoboundary AA (z ∘ K.subcomplexFaceEmbedding A hAK 2))
  rw [K.edgeCoboundary_subcomplex_restrict A hAK]

end Geometry.SimplicialComplex
