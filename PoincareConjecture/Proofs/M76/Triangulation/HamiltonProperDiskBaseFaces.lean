import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageIncidence
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks










set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}




theorem HamiltonProperDiskTriangulation.original_parameter_image
    (T : HamiltonProperDiskTriangulation R D b) :
    ∃ hi : InjOn T.inverse T.disk.space,
      (T.inverse_affine.embeddedImage hi).space = Cube := by
  have hi : InjOn T.inverse T.disk.space := by
    intro x hx y hy hxy
    have hxD := T.disk_space.subset hx
    have hyD := T.disk_space.subset hy
    have he : b.symm ⟨x, hxD⟩ = b.symm ⟨y, hyD⟩ := by
      apply Subtype.ext
      exact (T.inverse_eq ⟨x, hxD⟩).symm.trans
        (hxy.trans (T.inverse_eq ⟨y, hyD⟩))
    exact congrArg Subtype.val (b.symm.injective he)
  refine ⟨hi, ?_⟩
  rw [T.inverse_affine.embeddedImage_space]
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [T.inverse_eq ⟨x, T.disk_space.subset hx⟩]
    exact (b.symm ⟨x, T.disk_space.subset hx⟩).property
  · intro x hx
    refine ⟨b ⟨x, hx⟩, T.disk_space.symm.subset (b ⟨x, hx⟩).property, ?_⟩
    exact (T.inverse_eq (b ⟨x, hx⟩)).trans
      (congrArg Subtype.val (b.symm_apply_apply ⟨x, hx⟩))

private theorem pullback_full_coface
    (T : HamiltonProperDiskTriangulation R D b)
    (hi : InjOn T.inverse T.disk.space) {s : Finset E} (hs : s ∈ T.disk.faces)
    {t : Finset V2} (ht : t ∈ (T.inverse_affine.embeddedImage hi).faces)
    (hst : s.image T.inverse ⊆ t) (htcard : t.card = 3) :
    ∃ u ∈ T.disk.faces, s ⊆ u ∧ u.card = 3 ∧ u.image T.inverse = t := by
  classical
  rw [T.inverse_affine.embeddedImage_faces] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  refine ⟨u, hu, ?_, ?_, rfl⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (hst (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    exact hi (T.disk.subset_space hu hy) (T.disk.subset_space hs hx) hyx ▸ hy
  · exact (Finset.card_image_iff.mpr (hi.mono (T.disk.subset_space hu))).symm.trans htcard




theorem HamiltonProperDiskTriangulation.disk_face_card_le
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E} (hs : s ∈ T.disk.faces) :
    s.card ≤ 3 := by
  classical
  obtain ⟨hi, _⟩ := T.original_parameter_image
  let L := T.inverse_affine.embeddedImage hi
  have hsL : s.image T.inverse ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have hcard := (L.indep hsL).card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have himage : (s.image T.inverse).card = s.card :=
    Finset.card_image_iff.mpr (hi.mono (T.disk.subset_space hs))
  simpa only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, himage] using hcard




theorem HamiltonProperDiskTriangulation.exists_disk_triangle_coface
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E} (hs : s ∈ T.disk.faces) :
    ∃ t ∈ T.disk.faces, s ⊆ t ∧ t.card = 3 := by
  classical
  obtain ⟨hi, hspace⟩ := T.original_parameter_image
  let L := T.inverse_affine.embeddedImage hi
  have hL := T.inverse_affine.embeddedImage_finite hi (T.finite.subset T.disk_le)
  have hsL : s.image T.inverse ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have hcv : Convex ℝ L.space := hspace.symm ▸ convex_closedBall (0 : V2) 1
  have hint : (interior L.space).Nonempty := by
    rw [hspace, interior_closedBall']
    exact ⟨0, mem_ball_self zero_lt_one⟩
  obtain ⟨t, ht, hst, htc⟩ := L.exists_full_coface_of_convex_space hL hcv hint hsL
  obtain ⟨u, hu, hsu, huc, _⟩ := pullback_full_coface T hi hs ht hst (by simpa using htc)
  exact ⟨u, hu, hsu, huc⟩




theorem HamiltonProperDiskTriangulation.exists_boundary_triangle_coface
    (T : HamiltonProperDiskTriangulation R D b)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hscard : s.card = 2)
    (hboundary : convexHull ℝ (s : Set E) ⊆ frontier R) :
    ∃ t ∈ T.disk.faces, s ⊆ t ∧ t.card = 3 ∧
      ∀ u ∈ T.disk.faces, s ⊆ u → u.card = 3 → u = t := by
  classical
  obtain ⟨hi, hspace⟩ := T.original_parameter_image
  let L := T.inverse_affine.embeddedImage hi
  let q := s.image T.inverse
  have hq : q ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have hqc : q.card = Module.finrank ℝ V2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hscard] using
      (Finset.card_image_iff.mpr (hi.mono (T.disk.subset_space hs)))
  have hqfront : convexHull ℝ (q : Set V2) ⊆ frontier L.space := by
    intro y hy
    have hyim : y ∈ T.inverse '' convexHull ℝ (s : Set E) := by
      rw [T.inverse_affine.image_convexHull hs]
      simpa only [q, Finset.coe_image] using hy
    obtain ⟨x, hx, rfl⟩ := hyim
    have hxD := T.disk_space.subset (T.disk.convexHull_subset_space hs hx)
    have hbdy : (b.symm ⟨x, hxD⟩ : V2) ∈ sphere 0 1 :=
      (hproper (b.symm ⟨x, hxD⟩)).mp (by simpa only [b.apply_symm_apply] using hboundary hx)
    rw [hspace, frontier_closedBall', T.inverse_eq ⟨x, hxD⟩]
    exact hbdy
  obtain ⟨t, ht, hst, htc⟩ := T.exists_disk_triangle_coface hs
  refine ⟨t, ht, hst, htc, ?_⟩
  intro u hu hsu huc
  by_contra hne
  have htL : t.image T.inverse ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨t, ht, rfl⟩
  have huL : u.image T.inverse ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨u, hu, rfl⟩
  have htcL : (t.image T.inverse).card = Module.finrank ℝ V2 + 1 := by
    simpa [htc] using Finset.card_image_iff.mpr (hi.mono (T.disk.subset_space ht))
  have hucL : (u.image T.inverse).card = Module.finrank ℝ V2 + 1 := by
    simpa [huc] using Finset.card_image_iff.mpr (hi.mono (T.disk.subset_space hu))
  have hneL : t.image T.inverse ≠ u.image T.inverse := by
    intro he
    apply hne
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp
        (he.symm ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      exact hi (T.disk.subset_space ht hy) (T.disk.subset_space hu hx) hyx ▸ hy
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp
        (he ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      exact hi (T.disk.subset_space hu hy) (T.disk.subset_space ht hx) hyx ▸ hy
  obtain ⟨y, hy⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (q : Set V2))
    (Finset.coe_nonempty.mpr (L.nonempty_of_mem_faces hq)).convexHull
  have hyint := L.mem_interior_space_of_paired_facet hqc htL huL htcL hucL
    (Finset.image_subset_image hst) (Finset.image_subset_image hsu) hneL hy
  exact (hqfront (intrinsicInterior_subset hy)).2 hyint

end PoincareConjecture.M76.HamiltonIndexOne
