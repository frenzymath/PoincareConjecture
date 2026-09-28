import PoincareConjecture.Proofs.M76.Rigidity.OriginalProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarEdgeLink
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolygonLinkDualDisk

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

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

end PoincareConjecture.M76.OriginalProperDiskTriangulation
