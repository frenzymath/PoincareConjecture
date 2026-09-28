import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry











set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem exists_finite_triangulation_prod (K : SimplicialComplex ℝ E)
    (J : SimplicialComplex ℝ F) (hK : K.faces.Finite) (hJ : J.faces.Finite) :
    ∃ L : SimplicialComplex ℝ (E × F), L.faces.Finite ∧ L.space = K.space ×ˢ J.space ∧
      ∀ q ∈ L.faces, ∃ s ∈ K.faces, ∃ t ∈ J.faces,
        convexHull ℝ (q : Set (E × F)) ⊆
          convexHull ℝ (s : Set E) ×ˢ convexHull ℝ (t : Set F) := by
  classical
  let : Fintype K.faces := hK.fintype
  let : Fintype J.faces := hJ.fintype
  let π₁ : E × F →ᵃ[ℝ] E := (LinearMap.fst ℝ E F).toAffineMap
  let π₂ : E × F →ᵃ[ℝ] F := (LinearMap.snd ℝ E F).toAffineMap
  have hcell (i : K.faces × J.faces) :
      ∃ L : SimplicialComplex ℝ (E × F), L.faces.Finite ∧
        L.space = convexHull ℝ (i.1.val : Set E) ×ˢ convexHull ℝ (i.2.val : Set F) := by
    obtain ⟨H₁, hH₁⟩ := i.1.val.exists_affine_halfspaces_convexHull (K.indep i.1.property)
    obtain ⟨H₂, hH₂⟩ := i.2.val.exists_affine_halfspaces_convexHull (J.indep i.2.property)
    let H := H₁.image (fun a => a.comp π₁) ∪ H₂.image (fun a => a.comp π₂)
    have hrep : convexHull ℝ (i.1.val : Set E) ×ˢ convexHull ℝ (i.2.val : Set F) =
        {x | ∀ a ∈ H, a x ≤ 0} := by
      rw [hH₁, hH₂]
      ext x
      change ((∀ a ∈ H₁, a x.1 ≤ 0) ∧ (∀ a ∈ H₂, a x.2 ≤ 0)) ↔ _
      constructor
      · rintro ⟨hx, hy⟩ a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact hx b hb
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact hy b hb
      · intro hx
        exact ⟨fun a ha => hx (a.comp π₁)
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)),
          fun a ha => hx (a.comp π₂)
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))⟩
    exact ((i.1.val.finite_toSet.isCompact_convexHull ℝ).prod
      (i.2.val.finite_toSet.isCompact_convexHull ℝ)).exists_finite_triangulation_of_halfspaces
      H hrep
  choose C hC hspace using hcell
  obtain ⟨L, hL, hLs, hfaces⟩ := exists_finite_triangulation_iUnion C hC
  refine ⟨L, hL, hLs.trans ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [hspace i] at hi
      exact ⟨K.convexHull_subset_space i.1.property hi.1,
        J.convexHull_subset_space i.2.property hi.2⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
      obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx.2
      refine mem_iUnion.mpr ⟨(⟨s, hs⟩, ⟨t, ht⟩), ?_⟩
      rw [hspace]
      exact ⟨hxs, hxt⟩
  · intro q hq
    obtain ⟨i, r, hr, hqr⟩ := hfaces q hq
    refine ⟨i.1.val, i.1.property, i.2.val, i.2.property, ?_⟩
    exact (hqr.trans ((C i).convexHull_subset_space hr)).trans (hspace i).subset

end Geometry.SimplicialComplex
