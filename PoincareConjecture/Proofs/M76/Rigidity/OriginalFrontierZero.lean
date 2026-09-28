import PoincareConjecture.Proofs.M76.Rigidity.OriginalFrontierVertex
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBase

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem frontier_vertex_zero_data (p : (T.marked 2).vertices)
    (hpfront : (p : T.index → ℝ × V3) ∈ (T.marked 1).space) :
    ∃ a : Bool → (T.index → ℝ × V3), a false ≠ a true ∧
      IsFinitePLBallPair ℝ
        (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space)
        {a false, a true} ∧
      ContinuousOn (T.height p) ((T.vertexBlock p).space ∩ (T.marked 1).space) ∧
      ((T.vertexBlock p).space ∩ (T.marked 1).space) ∩ {x | T.height p x = 0} =
        T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space ∧
      (((T.vertexBlock p).space ∩ (T.marked 1).space) ∩
        ((T.vertexBlock p).link p).space) ∩ {x | T.height p x = 0} =
          {a false, a true} := by
  classical
  obtain ⟨u, v, huv, hA, _, hinter⟩ := T.exists_boundary_vertex_base_intervals p hpfront
  let a : Bool → (T.index → ℝ × V3) := fun k => if k then v else u
  let F := (T.vertexBlock p).space ∩ (T.marked 1).space
  let Q := F ∩ ((T.vertexBlock p).link p).space
  let A := T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space
  have hFU : F ⊆ T.dualRegion {(p : T.index → ℝ × V3)} :=
    fun _ hx => ⟨hx.1, T.boundary_space_subset_region hx.2⟩
  have hzero (x : T.index → ℝ × V3) (hx : x ∈ F) :
      T.height p x = 0 ↔ x ∈ (T.marked 2).space :=
    T.height_eq_zero_iff_on_dualRegion p (Finset.mem_singleton_self _) (hFU hx)
  have hAzero : F ∩ {x | T.height p x = 0} = A := by
    ext x
    constructor
    · intro hx
      exact ⟨(T.vertex_base_eq_inter p).symm.subset
        ⟨hx.1.1, (hzero x hx.1).mp hx.2⟩, hx.1.2⟩
    · intro hx
      have hxB := (T.vertex_base_eq_inter p).subset hx.1
      exact ⟨⟨hxB.1, hx.2⟩, (hzero x ⟨hxB.1, hx.2⟩).mpr hxB.2⟩
  have hAF : A ⊆ F :=
    fun _ hx => ⟨((T.vertex_base_eq_inter p).subset hx.1).1, hx.2⟩
  have hAQ : A ∩ Q = {u, v} := by
    rw [← hinter]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.1.1, hx.2.2⟩,
      fun hx => ⟨hx.1, hAF hx.1, hx.2.2⟩⟩
  have hQzero : Q ∩ {x | T.height p x = 0} = {u, v} := by
    rw [← hAQ]
    ext x
    exact ⟨fun hx => ⟨hAzero.subset ⟨hx.1.1, hx.2⟩, hx.1⟩,
      fun hx => ⟨hx.2, (hAzero.symm.subset hx.1).2⟩⟩
  exact ⟨a, huv, hA,
    (T.continuousOn_height_dualRegion p (Finset.mem_singleton_self _)).mono hFU,
    hAzero, hQzero⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
