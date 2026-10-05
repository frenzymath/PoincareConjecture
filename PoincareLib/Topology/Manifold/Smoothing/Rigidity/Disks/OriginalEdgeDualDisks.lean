import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalProperDiskTriangulation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.EmbeddedStarEdgeLink
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.Mathlib.PolygonLinkDualDisk

/-!
# Whole ambient dual disks of the original proper-disk edges

The same selected original chart produces the complete polygon face
link and hence the whole actual dual disk. Its old-boundary and normal
cuts remain separate. See Hudson1969, pp.58--63 and rigidity020, section5.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in
/-- Each actual disk edge has its complete ambient dual disk and
literal centroid-link boundary, produced by its original selected
chart. This makes no region-containment assertion. See rigidity020. -/
theorem isFinitePLBallPair_edge_dualBlock
    {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2) :
    let : Fintype T.ambient.faces := T.finite.fintype
    IsFinitePLBallPair (ℝ × ℝ) (T.ambient.barycentricDualBlock s).space
      ((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let pD : (T.marked 2).vertices := ⟨p, (T.marked 2).face_subset_vertices hs hps⟩
  have h3 : Module.finrank ℝ C3 = 3 := by simp [Module.finrank_prod]
  obtain ⟨n, P, hPi, hP, hPs⟩ := T.ambient.exists_polygon_faceLink_of_embedded_star
    T.finite h3 (T.marked_le 2 hs) hscard hps
    (fun x => T.chart (T.chart_index pD) (T.inverse x))
    (T.star_affine pD) (T.star_injective pD) (T.star_interior pD)
  exact T.ambient.isFinitePLBallPair_dualBlock_of_polygon_faceLink
    (T.marked_le 2 hs) P hPi hP hPs

end PoincareMT.M76.OriginalProperDiskTriangulation
