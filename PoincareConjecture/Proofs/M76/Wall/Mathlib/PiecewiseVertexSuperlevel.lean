import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {f : E → ℝ}





theorem AffineOnFaces.vertexSuperlevel_space (hf : K.AffineOnFaces f) (r : ℝ)
    (hside : ∀ s ∈ K.faces,
      (∀ v ∈ s, f v ≤ r) ∨ (∀ v ∈ s, r ≤ f v)) :
    (K.vertexSubcomplex {x | r ≤ f x}).space = K.space ∩ {x | r ≤ f x} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := hf s hs.1
    refine ⟨K.convexHull_subset_space hs.1 hxs, ?_⟩
    have hverts : (s : Set E) ⊆ a ⁻¹' Ici r := by
      intro v hv
      change r ≤ a v
      rw [← ha (subset_convexHull ℝ _ hv)]
      exact hs.2 v hv
    have hax : r ≤ a x :=
      convexHull_min hverts ((convex_Ici r).affine_preimage a.toAffineMap) hxs
    change r ≤ f x
    rwa [ha hxs]
  · rintro ⟨hx, hhigh⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    rcases hside s hs with hneg | hpos
    · obtain ⟨a, ha⟩ := hf s hs
      have hverts : (s : Set E) ⊆ a ⁻¹' Iic r := by
        intro v hv
        change a v ≤ r
        rw [← ha (subset_convexHull ℝ _ hv)]
        exact hneg v hv
      have hlow : a x ≤ r :=
        convexHull_min hverts ((convex_Iic r).affine_preimage a.toAffineMap) hxs
      have heq : a x = r := le_antisymm hlow (by rwa [← ha hxs])
      let B : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E r - a.toAffineMap
      have hB (v : E) (hv : v ∈ s) : 0 ≤ B v := by
        change 0 ≤ r - a v
        rw [← ha (subset_convexHull ℝ _ hv)]
        exact sub_nonneg.mpr (hneg v hv)
      have hBx : B x = 0 := by
        change r - a x = 0
        rw [heq, sub_self]
      have hzero := s.mem_convexHull_zero_vertices B hB hxs hBx
      let t := s.filter (fun v => f v = r)
      have hsub : (s : Set E) ∩ {v | B v = 0} ⊆ (t : Set E) := by
        intro v hv
        apply Finset.mem_filter.mpr
        refine ⟨hv.1, ?_⟩
        have hb : r - a v = 0 := hv.2
        exact (ha (subset_convexHull ℝ _ hv.1)).trans (sub_eq_zero.mp hb).symm
      have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hsub hzero
      have htne : t.Nonempty :=
        Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
      refine mem_space_iff.mpr ⟨t,
        ⟨K.down_closed hs (Finset.filter_subset _ _) htne, ?_⟩, hxt⟩
      intro v hv
      exact (Finset.mem_filter.mp hv).2.ge
    · exact mem_space_iff.mpr ⟨s, ⟨hs, hpos⟩, hxs⟩

end Geometry.SimplicialComplex
