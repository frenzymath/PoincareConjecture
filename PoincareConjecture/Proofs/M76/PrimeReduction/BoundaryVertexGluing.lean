import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexOverlap
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K L : SimplicialComplex ℝ E}
  [Fintype K.faces] [Fintype L.faces] {T : BoundaryTriangleFibers K L}
  {P : BoundaryEdgeFamily T}

local notation "I" => Icc (0 : ℝ) 1

theorem BoundaryVertexFamily.exists_whole_product (F : BoundaryVertexFamily P)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces) :
    ∃ H : (L.space ×ˢ I : Set (E × ℝ)) ≃ₜ (K.barycentricNeighborhood L).space,
      H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ L.space),
        (H ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x) ∧
      (∀ x : (L.space ×ˢ I : Set (E × ℝ)),
        (H x : E) ∈ L.space ↔ (x : E × ℝ).2 = 0) ∧
      ∀ (p : L.vertices)
        (x : ((L.barycentricDualBlock {(p : E)}).space ×ˢ I : Set (E × ℝ))),
        (H ⟨x, ⟨L.barycentricSubdivision_isSubdivision.space_eq.subset
          (space_subset_of_le (L.barycentricDualBlock_le {(p : E)}) x.property.1),
          x.property.2⟩⟩ : E) = F.chart p x := by
  classical
  let : Finite L.vertices := (L.finite_vertices_of_finite_faces (Set.toFinite L.faces)).to_subtype
  let W : L.vertices → Set E := fun p => (L.barycentricDualBlock {(p : E)}).space
  let N : L.vertices → Set E := fun p => (K.barycentricDualBlock {(p : E)}).space
  have hW : (⋃ p : L.vertices, W p) = L.space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact L.barycentricSubdivision_isSubdivision.space_eq.subset
        (space_subset_of_le (L.barycentricDualBlock_le {(p : E)}) hp)
    · intro x hx
      have hxN := L.space_subset_barycentricNeighborhood (L := L) le_rfl hx
      rw [L.barycentricNeighborhood_space_eq_iUnion_dualBlocks L] at hxN
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxN
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  have hN : (⋃ p : L.vertices, N p) = (K.barycentricNeighborhood L).space := by
    rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks L]
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨p, p.property, hp⟩
    · intro hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  have hWI : (⋃ p : L.vertices, W p ×ˢ I) = L.space ×ˢ I := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact ⟨hW.subset (mem_iUnion.mpr ⟨p, hp.1⟩), hp.2⟩
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp (hW.symm.subset hx.1)
      exact mem_iUnion.mpr ⟨p, hp, hx.2⟩
  obtain ⟨H, hH, hkeep⟩ := Homeomorph.exists_iUnion_finitePL
    (fun p : L.vertices => W p ×ˢ I) N F.chart F.piecewiseAffine
    (F.overlap_iff hfull) F.agrees
  let G := (Homeomorph.setCongr hWI.symm).trans (H.trans (Homeomorph.setCongr hN))
  have hG : G.IsFinitePL := by
    obtain ⟨g, hg, hval⟩ := hH
    refine ⟨g, ?_, ?_⟩
    · rwa [hWI] at hg
    · intro x
      exact hval ((Homeomorph.setCongr hWI.symm) x)
  have hGkeep (p : L.vertices) (x : (W p ×ˢ I : Set (E × ℝ))) :
      (G ⟨x, hWI.subset (mem_iUnion.mpr ⟨p, x.property⟩)⟩ : E) = F.chart p x :=
    hkeep p x
  refine ⟨G, hG, ?_, ?_, hGkeep⟩
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hW.symm.subset hx)
    exact (hGkeep p ⟨(x, 0), ⟨hp, le_rfl, zero_le_one⟩⟩).trans (F.central p x hp)
  · intro x
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hW.symm.subset x.property.1)
    have heq : (G x : E) = F.chart p ⟨x, ⟨hp, x.property.2⟩⟩ :=
      hGkeep p ⟨x, ⟨hp, x.property.2⟩⟩
    rw [heq]
    exact F.boundary p ⟨x, ⟨hp, x.property.2⟩⟩

end Geometry.SimplicialComplex
