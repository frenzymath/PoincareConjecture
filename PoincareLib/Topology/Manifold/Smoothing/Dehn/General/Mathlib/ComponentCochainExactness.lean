import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.OriginalEdgeComponent
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.SubcomplexIncidence

/-!
# Literal zero extension and edge exactness on an actual component

Every original coface of a retained face remains in the component.
A component cocycle therefore extends by zero to the whole original
complex, where an actual potential exists. Restriction returns that
same potential on the original component vertices. See Dehn derivation
019 and Hatcher, Algebraic Topology, pp. 104--107 and 189--190.
-/

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E) [Fintype K.vertices] [Fintype A.vertices]

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex

/-- A cocycle extends by zero when every original coface of a retained
face is retained. The incidence sum uses all three original edges.
See Dehn derivation 019. -/
theorem edgeCoboundary_zeroExtend_of_closed_cofaces (hAK : A ≤ K)
    (hcoface : ∀ {s t : Finset E}, s ∈ A.faces → t ∈ K.faces → s ⊆ t → t ∈ A.faces)
    (z : Edge AA → ZMod 2) (hz : edgeCoboundary AA z = 0) :
    edgeCoboundary KA (Function.extend (K.subcomplexFaceEmbedding A hAK 2) z 0) = 0 := by
  classical
  let : DecidableEq K.vertices := Classical.decEq K.vertices
  let i2 := K.subcomplexFaceEmbedding A hAK 2
  let i3 := K.subcomplexFaceEmbedding A hAK 3
  let ze := Function.extend i2 z 0
  have hrestrict : ze ∘ i2 = z := by
    funext q
    exact i2.injective.extend_apply z 0 q
  funext t
  change edgeCoboundary KA ze t = 0
  by_cases ht : t ∈ Set.range i3
  · obtain ⟨q, rfl⟩ := ht
    calc
      edgeCoboundary KA ze (i3 q) = edgeCoboundary AA (ze ∘ i2) q :=
        (congrFun (K.edgeCoboundary_subcomplex_restrict A hAK ze) q).symm
      _ = 0 := by rw [hrestrict, hz]; rfl
  · rw [edgeCoboundary_apply]
    apply Finset.sum_eq_zero
    intro e he
    have hne : ¬∃ q, i2 q = e := by
      rintro ⟨q, rfl⟩
      apply ht
      apply (K.subcomplexFaceEmbedding_range_iff A hAK 3 t).mpr
      have hsub : (i2 q).val ⊆ t.val := (Finset.mem_filter.mp he).2
      have hgeom : (i2 q).val.map (Function.Embedding.subtype _) ⊆
          t.val.map (Function.Embedding.subtype _) := Finset.map_subset_map.mpr hsub
      change (K.subcomplexFaceEmbedding A hAK 2 q).val.map
        (Function.Embedding.subtype _) ⊆ t.val.map (Function.Embedding.subtype _) at hgeom
      rw [K.subcomplexFaceEmbedding_forget] at hgeom
      exact hcoface q.property.1 t.property.1 hgeom
    exact Function.extend_apply' (f := (i2 : Edge AA → Edge KA))
      z (0 : Edge KA → ZMod 2) e hne

/-- Restrict the actual original potential of the zero-extended
cocycle. This proves exactness on the entire retained subcomplex.
See Dehn derivation 019. -/
theorem edge_incidence_exact_of_closed_cofaces (hAK : A ≤ K)
    (hcoface : ∀ {s t : Finset E}, s ∈ A.faces → t ∈ K.faces → s ⊆ t → t ∈ A.faces)
    (hexact : LinearMap.ker (edgeCoboundary KA) = LinearMap.range (vertexCoboundary KA)) :
    LinearMap.ker (edgeCoboundary AA) = LinearMap.range (vertexCoboundary AA) := by
  classical
  apply le_antisymm
  · intro z hz
    let i2 := K.subcomplexFaceEmbedding A hAK 2
    let ze := Function.extend i2 z 0
    have hze : ze ∈ LinearMap.ker (edgeCoboundary KA) :=
      K.edgeCoboundary_zeroExtend_of_closed_cofaces A hAK hcoface z hz
    rw [hexact] at hze
    obtain ⟨a, ha⟩ := hze
    refine ⟨a ∘ K.subcomplexVertexEmbedding A hAK, ?_⟩
    rw [K.vertexCoboundary_subcomplex_restrict A hAK, ha]
    funext e
    exact i2.injective.extend_apply z 0 e
  · rintro z ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary AA a

variable [DecidableEq E]

/-- The actual edge-graph component inherits exactness from the same
original whole boundary, using its proved full coface retention.
See Dehn derivation 019. -/
theorem edgeComponentComplex_edge_exactness
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (K.edgeComponentComplex C).vertices]
    (hexact : LinearMap.ker (edgeCoboundary KA) = LinearMap.range (vertexCoboundary KA)) :
    let L := (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex
    LinearMap.ker (edgeCoboundary L) = LinearMap.range (vertexCoboundary L) :=
  K.edge_incidence_exact_of_closed_cofaces (K.edgeComponentComplex C)
    (K.edgeComponentComplex_le C) (fun hs ht hst => K.edgeComponentComplex_coface C hs ht hst)
    hexact

end Geometry.SimplicialComplex
