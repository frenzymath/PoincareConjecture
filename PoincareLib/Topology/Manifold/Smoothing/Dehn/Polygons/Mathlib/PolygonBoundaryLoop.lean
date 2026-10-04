import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonSliceCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexSubtypePaths

/-!
# The original ordered-edge loop in the whole polygon boundary

Repeat only the first vertex at the end of the finite list and
concatenate the original straight edges inside the polygon-boundary
subtype. The complete closing edge is retained. See Dehn derivation
025, section 4.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (P : Polygon E (n + 3))

/-- The actual cyclic vertex list, with only the first vertex
repeated at the final index. See Dehn025, section 4. -/
def closedBoundaryVertices : Fin (n + 4) → P.boundary ℝ :=
  Fin.snoc (fun i => ⟨P i, P.vertex_mem_boundary i⟩) ⟨P 0, P.vertex_mem_boundary 0⟩

/-- Every nonfinal list entry is its original labelled vertex.
See Dehn025, section 4. -/
theorem closedBoundaryVertices_castSucc (i : Fin (n + 3)) :
    (P.closedBoundaryVertices i.castSucc : E) = P i := by
  simp [closedBoundaryVertices]

/-- The first list entry is exactly the original base vertex.
See Dehn025, section 4. -/
theorem closedBoundaryVertices_zero :
    P.closedBoundaryVertices 0 = ⟨P 0, P.vertex_mem_boundary 0⟩ := by
  simp [closedBoundaryVertices]

/-- The final list entry is the repeated original base vertex.
See Dehn025, section 4. -/
theorem closedBoundaryVertices_last :
    P.closedBoundaryVertices (Fin.last (n + 3)) = ⟨P 0, P.vertex_mem_boundary 0⟩ := by
  simp [closedBoundaryVertices]

/-- The successor list entry is the actual cyclic next vertex,
including the final-to-first edge. See Dehn025, section 4. -/
theorem closedBoundaryVertices_succ (i : Fin (n + 3)) :
    (P.closedBoundaryVertices i.succ : E) = P (finRotate (n + 3) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [closedBoundaryVertices]
  · have hrot : finRotate (n + 3) j.castSucc = j.succ := finRotate_of_lt (by omega)
    rw [hrot]
    exact P.closedBoundaryVertices_castSucc j.succ

/-- Each original closed polygon edge as a path in the whole
polygon-boundary subtype. See Dehn025, section 4. -/
noncomputable def closedBoundaryEdgePath (i : Fin (n + 3)) :
    Path (P.closedBoundaryVertices i.castSucc) (P.closedBoundaryVertices i.succ) :=
  Path.segmentIn (P.boundary ℝ) _ _ (by
    rw [P.closedBoundaryVertices_castSucc, P.closedBoundaryVertices_succ]
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨i, by simpa only [edgeSet, affineSegment_eq_segment] using hx⟩)

/-- The literal finite ordered-edge traversal is a based loop
inside the complete polygon boundary. See Dehn025, section 4. -/
noncomputable def boundaryLoop :
    Path (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ)
      ⟨P 0, P.vertex_mem_boundary 0⟩ :=
  (Path.concat P.closedBoundaryVertices P.closedBoundaryEdgePath).cast
    P.closedBoundaryVertices_zero.symm P.closedBoundaryVertices_last.symm

end Polygon
