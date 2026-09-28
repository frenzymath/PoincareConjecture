import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskRim









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)



theorem disk_parameter_image :
    InjOn T.parameter (T.marked 2).space ∧ T.parameter '' (T.marked 2).space = D := by
  rw [T.disk_space]
  exact intrinsic_disk_parameter_image T.graph j T.parameter T.parameter_original



theorem rim_space_subsets :
    (T.marked 3).space ⊆ (T.marked 2).space ∧
      (T.marked 3).space ⊆ (T.marked 1).space := by
  rw [← T.disk_boundary_inter]
  exact ⟨inter_subset_left, inter_subset_right⟩



theorem parameter_mem_rim_iff {x : T.index → ℝ × V3}
    (hx : x ∈ (T.marked 2).space) : T.parameter x ∈ Q ↔ x ∈ (T.marked 3).space := by
  obtain ⟨hi, _⟩ := T.disk_parameter_image
  obtain ⟨_, hQ⟩ := T.rim_parameter_image
  constructor
  · intro hxQ
    obtain ⟨y, hy, hyx⟩ := hQ.symm.subset hxQ
    exact hi (T.rim_space_subsets.1 hy) hx hyx ▸ hy
  · intro hxQ
    exact hQ.subset (mem_image_of_mem T.parameter hxQ)



theorem disk_space_subset_region : (T.marked 2).space ⊆ (T.marked 0).space := by
  intro x hx
  have hxK : x ∈ T.ambient.space := SimplicialComplex.space_subset_of_le (T.marked_le 2) hx
  obtain ⟨hz, hjz⟩ := T.parameter_disk_point hx
  exact (T.inverse_mem_region_iff hxK).mp (hjz ▸ T.disk_in_region hz)




theorem rim_le_disk : T.marked 3 ≤ T.marked 2 := by
  intro s hs
  apply T.marked_full 2 s (T.marked_le 3 hs)
  intro x hx
  have hxK := T.ambient.face_subset_vertices (T.marked_le 3 hs) hx
  exact (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 2) hxK).mp
    (T.rim_space_subsets.1 ((T.marked 3).subset_space hs hx))



theorem rim_le_boundary : T.marked 3 ≤ T.marked 1 := by
  intro s hs
  apply T.marked_full 1 s (T.marked_le 3 hs)
  intro x hx
  have hxK := T.ambient.face_subset_vertices (T.marked_le 3 hs) hx
  exact (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 1) hxK).mp
    (T.rim_space_subsets.2 ((T.marked 3).subset_space hs hx))




theorem disk_face_mem_boundary_iff {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) :
    s ∈ (T.marked 1).faces ↔ s ∈ (T.marked 3).faces := by
  constructor
  · intro hsB
    apply T.marked_full 3 s (T.marked_le 2 hs)
    intro x hx
    have hxK := T.ambient.face_subset_vertices (T.marked_le 2 hs) hx
    apply (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 3) hxK).mp
    exact T.disk_boundary_inter ▸
      ⟨(T.marked 2).subset_space hs hx, (T.marked 1).subset_space hsB hx⟩
  · exact fun hsQ => T.rim_le_boundary hsQ

end PoincareConjecture.M76.OriginalProperDiskTriangulation
