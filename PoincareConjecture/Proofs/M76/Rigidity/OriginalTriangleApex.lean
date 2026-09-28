import PoincareConjecture.Proofs.M76.Rigidity.OriginalRegionCofaces









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)



theorem exists_triangle_coface_apex
    {s t : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 3) (ht : t ∈ T.ambient.faces) (htcard : t.card = 4)
    (hst : s ⊆ t) :
    ∃ v, v ∉ s ∧ insert v s = t ∧ v ∉ (T.marked 2).space := by
  classical
  obtain ⟨v, hvs, hvt⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hst, (show s.card + 1 = t.card by omega)⟩
  refine ⟨v, hvs, hvt, ?_⟩
  intro hvD
  have hvt' : v ∈ t := hvt ▸ Finset.mem_insert_self v s
  have hvK := T.ambient.face_subset_vertices ht hvt'
  have hv : v ∈ (T.marked 2).vertices :=
    (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 2) hvK).mp hvD
  have htD : t ∈ (T.marked 2).faces := by
    apply T.marked_full 2 t ht
    intro z hz
    rw [← hvt] at hz
    rcases Finset.mem_insert.mp hz with rfl | hzs
    · exact hv
    · exact (T.marked 2).face_subset_vertices hs hzs
  have hbound := T.disk_face_card_le htD
  omega

end PoincareConjecture.M76.OriginalProperDiskTriangulation
