import PoincareConjecture.Proofs.M34.Mathlib.CompactPartialImage

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y)

theorem image_interior_eq_of_subset_source {S : Set X} (hS : S ⊆ e.source) :
    e '' interior S = interior (e '' S) := by
  have hi := (e.isImage_image_of_subset_source hS).interior
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hi.apply_mem_iff (hS (interior_subset hx))).mpr hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    exact ⟨x, (hi.apply_mem_iff (hS hx)).mp hy, rfl⟩

theorem image_sdiff_eq_of_subset_source {S T : Set X}
    (hS : S ⊆ e.source) (hT : T ⊆ e.source) :
    e '' (S \ T) = e '' S \ e '' T := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    rintro ⟨z, hz, he⟩
    exact hxT ((e.injOn (hT hz) (hS hxS) he) ▸ hz)
  · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
    exact ⟨x, ⟨hx, fun ht => hnot ⟨x, ht, rfl⟩⟩, rfl⟩

theorem image_inter_frontier_eq_of_subset_source {S T : Set X}
    (hS : S ⊆ e.source) (hT : T ⊆ e.source) :
    e '' (S ∩ frontier T) = e '' S ∩ frontier (e '' T) := by
  have hf := (e.isImage_image_of_subset_source hT).frontier
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxT⟩, rfl⟩
    exact ⟨⟨x, hxS, rfl⟩, (hf.apply_mem_iff (hS hxS)).mpr hxT⟩
  · rintro ⟨⟨x, hxS, rfl⟩, hxT⟩
    exact ⟨x, ⟨hxS, (hf.apply_mem_iff (hS hxS)).mp hxT⟩, rfl⟩

end OpenPartialHomeomorph
