import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFrontierVertex
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBase
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLowerProducts









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}




theorem HamiltonProperDiskTriangulation.frontier_vertex_zero_data
    (T : HamiltonProperDiskTriangulation R D b) {c : E ≃ᴬ[ℝ] V}
    (C : HamiltonProperDiskCoherentSides T c) (p : T.disk.vertices)
    (hpfront : (p : E) ∈ frontier R) :
    ∃ a : Bool → E, a false ≠ a true ∧
      IsFinitePLBallPair ℝ (T.diskVertexBlock p ∩ frontier R) {a false, a true} ∧
      ContinuousOn (C.labels.height p) ((T.vertexBlock p).space ∩ frontier R) ∧
      ((T.vertexBlock p).space ∩ frontier R) ∩ {x | C.labels.height p x = 0} =
        T.diskVertexBlock p ∩ frontier R ∧
      (((T.vertexBlock p).space ∩ frontier R) ∩ ((T.vertexBlock p).link p).space) ∩
          {x | C.labels.height p x = 0} = {a false, a true} := by
  obtain ⟨u, v, huv, hA, _, hinter⟩ :=
    T.exists_boundary_vertex_base_intervals p hpfront
  let a : Bool → E := fun j => if j then v else u
  let F := (T.vertexBlock p).space ∩ frontier R
  let Q := F ∩ ((T.vertexBlock p).link p).space
  let A := T.diskVertexBlock p ∩ frontier R
  have hsource : (T.vertexBlock p).space ⊆ (T.pairChart p).chart.source :=
    (T.vertexBlock_centered_chart p).2.2.2.1
  have hRclosed : IsClosed R := T.region_space ▸
    (T.region.isCompact_space_of_finite (T.finite.subset T.region_le)).isClosed
  have hzero (x : E) (hx : x ∈ F) : C.labels.height p x = 0 ↔ x ∈ D :=
    C.labels.height_eq_zero_iff p (hsource hx.1) (hRclosed.frontier_subset hx.2)
  have hAzero : F ∩ {x | C.labels.height p x = 0} = A := by
    ext x
    constructor
    · intro hx
      exact ⟨(T.diskVertexBlock_eq_inter p).symm.subset
        ⟨hx.1.1, (hzero x hx.1).mp hx.2⟩, hx.1.2⟩
    · intro hx
      have hxB := (T.diskVertexBlock_eq_inter p).subset hx.1
      exact ⟨⟨hxB.1, hx.2⟩, (hzero x ⟨hxB.1, hx.2⟩).mpr hxB.2⟩
  have hAF : A ⊆ F := by
    intro x hx
    exact ⟨((T.diskVertexBlock_eq_inter p).subset hx.1).1, hx.2⟩
  have hAQ : A ∩ Q = {u, v} := by
    rw [← hinter]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.1.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, hAF hx.1, hx.2.2⟩
  have hQzero : Q ∩ {x | C.labels.height p x = 0} = {u, v} := by
    rw [← hAQ]
    ext x
    constructor
    · exact fun hx => ⟨hAzero.subset ⟨hx.1.1, hx.2⟩, hx.1⟩
    · exact fun hx => ⟨hx.2, (hAzero.symm.subset hx.1).2⟩
  refine ⟨a, huv, hA, (C.labels.continuousOn_height p).mono
    (inter_subset_left.trans hsource), hAzero, hQzero⟩

end PoincareConjecture.M76.HamiltonIndexOne
