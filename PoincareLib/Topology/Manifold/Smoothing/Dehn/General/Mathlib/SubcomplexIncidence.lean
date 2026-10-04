import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.SubcomplexFaceInclusion

/-!
# Original incidence commutes with the whole boundary inclusion

Every vertex and lower face of a marked simplex is retained by the
actual subcomplex map. Thus restriction commutes with the literal
incidence sums, and dual inclusion commutes with both boundary maps.
See Dehn derivation 018 and Hatcher pp. 104--107 and 189--190.
-/

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E)

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex

/-- Restriction retains both original endpoints of every marked edge.
See Dehn derivation 018. -/
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

/-- The actual first chain boundary commutes with inclusion on every
original marked edge chain. See Dehn derivation 018. -/
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
/-- The full edge set of each marked triangle is exactly the image
of its full original edge set. See Dehn derivation 018. -/
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

/-- Restriction retains all original edge terms of every marked
triangle, with no support loss. See Dehn derivation 018. -/
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

/-- The actual second boundary commutes with the whole marked chain
inclusion on the original triangle labels. See Dehn derivation 018. -/
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
