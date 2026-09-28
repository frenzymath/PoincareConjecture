import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (P : Polygon E (n + 3))

def closedBoundaryVertices : Fin (n + 4) → P.boundary ℝ :=
  Fin.snoc (fun i => ⟨P i, P.vertex_mem_boundary i⟩) ⟨P 0, P.vertex_mem_boundary 0⟩

theorem closedBoundaryVertices_castSucc (i : Fin (n + 3)) :
    (P.closedBoundaryVertices i.castSucc : E) = P i := by
  simp [closedBoundaryVertices]

theorem closedBoundaryVertices_zero :
    P.closedBoundaryVertices 0 = ⟨P 0, P.vertex_mem_boundary 0⟩ := by
  simp [closedBoundaryVertices]

theorem closedBoundaryVertices_last :
    P.closedBoundaryVertices (Fin.last (n + 3)) = ⟨P 0, P.vertex_mem_boundary 0⟩ := by
  simp [closedBoundaryVertices]

theorem closedBoundaryVertices_succ (i : Fin (n + 3)) :
    (P.closedBoundaryVertices i.succ : E) = P (finRotate (n + 3) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [closedBoundaryVertices]
  · have hrot : finRotate (n + 3) j.castSucc = j.succ := finRotate_of_lt (by omega)
    rw [hrot]
    exact P.closedBoundaryVertices_castSucc j.succ

noncomputable def closedBoundaryEdgePath (i : Fin (n + 3)) :
    Path (P.closedBoundaryVertices i.castSucc) (P.closedBoundaryVertices i.succ) :=
  Path.segmentIn (P.boundary ℝ) _ _ (by
    rw [P.closedBoundaryVertices_castSucc, P.closedBoundaryVertices_succ]
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨i, by simpa only [edgeSet, affineSegment_eq_segment] using hx⟩)

noncomputable def boundaryLoop :
    Path (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ)
      ⟨P 0, P.vertex_mem_boundary 0⟩ :=
  (Path.concat P.closedBoundaryVertices P.closedBoundaryEdgePath).cast
    P.closedBoundaryVertices_zero.symm P.closedBoundaryVertices_last.symm

end Polygon
