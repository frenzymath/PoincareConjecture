import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBaseFaces

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

theorem HamiltonProperDiskTriangulation.disk_triangle_not_boundary
    (T : HamiltonProperDiskTriangulation R D b)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 3) :
    s ∉ T.boundary.faces := by
  classical
  intro hsF
  obtain ⟨hi, hspace⟩ := T.original_parameter_image
  let L := T.inverse_affine.embeddedImage hi
  let q := s.image T.inverse
  have hq : q ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have hqc : q.card = Module.finrank ℝ V2 + 1 := by
    simpa [hcard] using Finset.card_image_iff.mpr
      (hi.mono (T.disk.subset_space hs))
  have hqfront : convexHull ℝ (q : Set V2) ⊆ frontier L.space := by
    intro y hy
    have hyim : y ∈ T.inverse '' convexHull ℝ (s : Set E) := by
      rw [T.inverse_affine.image_convexHull hs]
      simpa only [q, Finset.coe_image] using hy
    obtain ⟨x, hx, rfl⟩ := hyim
    have hxD := T.disk_space.subset (T.disk.convexHull_subset_space hs hx)
    have hxF := T.boundary_space.subset (T.boundary.convexHull_subset_space hsF hx)
    have hbdy : (b.symm ⟨x, hxD⟩ : V2) ∈ sphere 0 1 :=
      (hproper (b.symm ⟨x, hxD⟩)).mp (by simpa only [b.apply_symm_apply] using hxF)
    rw [hspace, frontier_closedBall', T.inverse_eq ⟨x, hxD⟩]
    exact hbdy
  obtain ⟨y, hy⟩ := Set.Nonempty.intrinsicInterior
    (convex_convexHull ℝ (q : Set V2))
    (Finset.coe_nonempty.mpr (L.nonempty_of_mem_faces hq)).convexHull
  exact (hqfront (intrinsicInterior_subset hy)).2
    (L.mem_interior_space_of_full_face hq hqc hy)

end PoincareConjecture.M76.HamiltonIndexOne
