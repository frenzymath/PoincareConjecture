import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChainInclusion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChainCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SubcomplexIncidence

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E) [Fintype K.vertices] [Fintype A.vertices]

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex

open Classical in

theorem subcomplex_totalTriangleChain (hAK : A ≤ K) :
    (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (K.subcomplexFaceEmbedding A hAK 3)).dualMap (totalTriangleChain AA) =
      markedTriangleChain KA
        (fun t => t.val.map (Function.Embedding.subtype _) ∈ A.faces) := by
  classical
  apply LinearMap.ext
  intro f
  change totalTriangleChain AA (f ∘ K.subcomplexFaceEmbedding A hAK 3) = _
  rw [totalTriangleChain_apply, markedTriangleChain_apply]
  apply Finset.sum_bij (fun t _ => K.subcomplexFaceEmbedding A hAK 3 t)
  · intro t _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [K.subcomplexFaceEmbedding_forget]
    exact t.property.1
  · intro t _ u _ h
    exact (K.subcomplexFaceEmbedding A hAK 3).injective h
  · intro q hq
    obtain ⟨t, ht⟩ := (K.subcomplexFaceEmbedding_range_iff A hAK 3 q).mpr
      (Finset.mem_filter.mp hq).2
    exact ⟨t, Finset.mem_univ _, ht⟩
  · intro t _
    rfl

omit [Fintype K.vertices] [Fintype A.vertices] in
open Classical in

theorem subcomplex_triangleChain_range_iff [Finite K.vertices] (hAK : A ≤ K)
    (c : Module.Dual (ZMod 2) (Triangle KA → ZMod 2)) :
    c ∈ LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (K.subcomplexFaceEmbedding A hAK 3)).dualMap ↔
      ∀ t : Triangle KA,
        t.val.map (Function.Embedding.subtype _) ∉ A.faces → c (Pi.single t 1) = 0 := by
  let : Fintype K.vertices := Fintype.ofFinite _
  rw [dual_restrict_range_iff]
  simp only [K.subcomplexFaceEmbedding_range_iff A hAK 3]
  constructor
  · intro h t ht
    convert h t ht using 1
    congr 1
    funext q
    by_cases hq : q = t <;> simp [hq]
  · intro h t ht
    convert h t ht using 1
    congr 1
    funext q
    by_cases hq : q = t <;> simp [hq]

omit [Fintype A.vertices] in

theorem subcomplex_markedTriangleChain_ne_zero (hAK : A ≤ K) (t : Triangle AA) :
    markedTriangleChain KA
      (fun q => q.val.map (Function.Embedding.subtype _) ∈ A.faces) ≠ 0 := by
  classical
  have ht : (K.subcomplexFaceEmbedding A hAK 3 t).val.map
      (Function.Embedding.subtype _) ∈ A.faces := by
    rw [K.subcomplexFaceEmbedding_forget]
    exact t.property.1
  intro h
  have hz := markedTriangleChain_single KA
    (fun q => q.val.map (Function.Embedding.subtype _) ∈ A.faces)
    (K.subcomplexFaceEmbedding A hAK 3 t)
  rw [h, LinearMap.zero_apply, if_pos ht] at hz
  exact zero_ne_one hz

end Geometry.SimplicialComplex
