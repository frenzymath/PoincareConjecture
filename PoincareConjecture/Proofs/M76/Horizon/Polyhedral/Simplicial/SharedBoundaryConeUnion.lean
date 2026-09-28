import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

omit [IsStrictOrderedRing 𝕜] in
theorem space_inf_eq_inter_of_le (R L M : SimplicialComplex 𝕜 E)
    (hLR : L ≤ R) (hMR : M ≤ R) : (L ⊓ M).space = L.space ∩ M.space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact ⟨mem_space_iff.mpr ⟨s, hs.1, hxs⟩, mem_space_iff.mpr ⟨s, hs.2, hxs⟩⟩
  · rintro x ⟨hxL, hxM⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxL
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxM
    have hxi : x ∈ convexHull 𝕜 ((s ∩ t : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using R.inter_subset_convexHull (hLR hs) (hMR ht) ⟨hxs, hxt⟩
    have hne : (s ∩ t).Nonempty := by
      exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxi⟩)
    exact mem_space_iff.mpr ⟨s ∩ t,
      ⟨L.down_closed hs Finset.inter_subset_left hne,
        M.down_closed ht Finset.inter_subset_right hne⟩, hxi⟩

theorem cross_inter_subset_of_shared_boundary (R L M C D : SimplicialComplex 𝕜 E)
    (hLR : L ≤ R) (hMR : M ≤ R) (hLC : L ≤ C) (hMD : M ≤ D)
    (hinter : C.space ∩ D.space ⊆ L.space ∩ M.space)
    {s t : Finset E} (hs : s ∈ C.faces) (ht : t ∈ D.faces) :
    convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 (t : Set E) ⊆
      convexHull 𝕜 ((s : Set E) ∩ t) := by
  apply C.cross_inter_subset_of_common_subcomplex D (L ⊓ M)
    (le_trans inf_le_left hLC) (le_trans inf_le_right hMD) ?_ hs ht
  rw [R.space_inf_eq_inter_of_le L M hLR hMR]
  exact hinter

end Geometry.SimplicialComplex
