import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SubcomplexTriangleChains
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.RelativeTetrahedronChains

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E) [Fintype K.vertices] [Fintype A.vertices]

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex

noncomputable def subcomplexTopCycles (hAK : A ≤ K) :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) (Triangle KA → ZMod 2)) :=
  Submodule.map
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (K.subcomplexFaceEmbedding A hAK 3)).dualMap
    (LinearMap.ker (edgeCoboundary AA).dualMap)

theorem subcomplexTopCycles_le_ker (hAK : A ≤ K) :
    K.subcomplexTopCycles A hAK ≤ LinearMap.ker (edgeCoboundary KA).dualMap := by
  rintro z ⟨c, hc, rfl⟩
  change (edgeCoboundary KA).dualMap
    ((LinearMap.funLeft (ZMod 2) (ZMod 2)
      (K.subcomplexFaceEmbedding A hAK 3)).dualMap c) = 0
  rw [K.boundary2_subcomplex_include A hAK]
  have hz : (edgeCoboundary AA).dualMap c = 0 := hc
  rw [hz, map_zero]

open Classical in

theorem subcomplexTopCycles_inf_tetrahedron_boundaries (hAK : A ≤ K)
    (hcofaces : ∀ t : Triangle KA, (tetrahedronCofaces KA t).card =
      if t.val.map (Function.Embedding.subtype _) ∈ A.faces then 1 else 2)
    (hconn : (tetrahedronGraph KA).Connected)
    (hboundaryCofaces : ∀ e : Edge AA, (triangleCofaces AA e).card = 2) :
    K.subcomplexTopCycles A hAK ⊓ LinearMap.range (triangleCoboundary KA).dualMap =
      Submodule.span (ZMod 2) {markedTriangleChain KA
        (fun t => t.val.map (Function.Embedding.subtype _) ∈ A.faces)} := by
  classical
  let B : Triangle KA → Prop := fun t =>
    t.val.map (Function.Embedding.subtype _) ∈ A.faces
  apply le_antisymm
  · rintro z ⟨⟨d, _hd, hdz⟩, ⟨c, hcz⟩⟩
    have hsupport : ∀ t : Triangle KA, ¬ B t →
        (triangleCoboundary KA).dualMap c (Pi.single t 1) = 0 := by
      apply (K.subcomplex_triangleChain_range_iff A hAK _).mp
      exact ⟨d, hdz.trans hcz.symm⟩
    obtain ⟨r, _hr, hb⟩ := exists_scalar_total_of_relative_boundary KA B
      hcofaces hconn c (by
        intro t ht
        apply Eq.trans _ (hsupport t ht)
        congr 1
        funext q
        by_cases hq : q = t <;> simp [hq])
    rw [← hcz, hb]
    exact Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    constructor
    · exact ⟨totalTriangleChain AA, boundary2_total_eq_zero_of_two AA hboundaryCofaces,
        K.subcomplex_totalTriangleChain A hAK⟩
    · exact ⟨totalTetrahedronChain KA, boundary3_total_eq_marked KA B hcofaces⟩

end Geometry.SimplicialComplex
