import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

theorem Topology.IsOpenEmbedding.compactCut_topology
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f)
    {s k b : Set X} (hs : IsOpen s) (hcl : closure s = k)
    (hi : interior k = s) (hfr : frontier k = b) (hk : IsCompact k) :
    IsOpen (f '' s) ∧ closure (f '' s) = f '' k ∧
      interior (f '' k) = f '' s ∧ frontier (f '' s) = f '' b ∧
      frontier (f '' k) = f '' b ∧
      frontier (range f) ⊆ closure (f '' kᶜ) := by
  have hkclosed : IsClosed (f '' k) := (hk.image hf.continuous).isClosed
  have hsk : s ⊆ k := hcl ▸ subset_closure
  have hclosure : closure (f '' s) = f '' k := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono hsk) hkclosed
    · rw [← hcl]
      exact image_closure_subset_closure_image hf.continuous
  have hinterior : interior (f '' k) = f '' s := by
    have hp : f ⁻¹' interior (f '' k) = s := by
      rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
        preimage_image_eq _ hf.injective, hi]
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, _, rfl⟩ := interior_subset hy
      exact ⟨x, hp ▸ hy, rfl⟩
    · rw [← hi]
      exact hf.isOpenMap.image_interior_subset k
  have hfrontK : frontier (f '' k) = f '' b := by
    have hp : f ⁻¹' frontier (f '' k) = b := by
      rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
        preimage_image_eq _ hf.injective, hfr]
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, _, rfl⟩ := hkclosed.frontier_subset hy
      exact ⟨x, hp ▸ hy, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      change x ∈ f ⁻¹' frontier (f '' k)
      rwa [hp]
  refine ⟨hf.isOpenMap _ hs, hclosure, hinterior, ?_, hfrontK, ?_⟩
  · rw [(hf.isOpenMap _ hs).frontier_eq, hclosure, ← hfrontK,
      frontier, hkclosed.closure_eq, hinterior]
  · have hcover : range f = (f '' k) ∪ (f '' kᶜ) := by
      rw [← image_union, union_compl_self, image_univ]
    intro y hy
    have hycl := frontier_subset_closure hy
    have hyn : y ∉ range f := (hf.isOpen_range.frontier_eq ▸ hy).2
    rw [hcover, closure_union, hkclosed.closure_eq] at hycl
    exact hycl.resolve_left fun ⟨x, _, hx⟩ => hyn ⟨x, hx⟩
