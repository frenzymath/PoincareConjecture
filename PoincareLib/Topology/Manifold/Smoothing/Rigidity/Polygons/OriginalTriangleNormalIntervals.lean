import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalProperDiskTriangulation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.EmbeddedStarDualInterval

/-!
# Actual whole normal intervals of the original disk triangles

The selected original chart-star embedding supplies the two ambient
tetrahedra and the complete dual interval in the same graph complex.
See rigidity017--018 and Hudson1969, pp.58--63.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in
/-- Each actual disk triangle has its complete ambient dual interval
with the two actual tetrahedron centroids as boundary. The graph ambient
dimension is unrestricted. See rigidity018, section4. -/
theorem exists_triangle_normal_interval {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 3) :
    let : Fintype T.ambient.faces := T.finite.fintype
    ∃ t ∈ T.ambient.faces, ∃ u ∈ T.ambient.faces,
      s ⊆ t ∧ s ⊆ u ∧ t.card = 4 ∧ u.card = 4 ∧ t ≠ u ∧
      (∀ v ∈ T.ambient.faces, s ⊆ v → v.card = 4 → v = t ∨ v = u) ∧
      IsFinitePLBallPair ℝ (T.ambient.barycentricDualBlock s).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      s.centroid ℝ id ∈ (T.ambient.barycentricDualBlock s).space \
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      ((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, u.centroid ℝ id} := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let pD : (T.marked 2).vertices := ⟨p, (T.marked 2).face_subset_vertices hs hps⟩
  have hc : s.card = Module.finrank ℝ C3 := by
    simpa [Module.finrank_prod] using hscard
  have h := T.ambient.exists_dual_interval_of_embedded_star
    (T.marked_le 2 hs) hc hps (fun x => T.chart (T.chart_index pD) (T.inverse x))
    (T.star_affine pD) (T.star_injective pD) (T.star_interior pD)
  simpa [Module.finrank_prod] using h

end PoincareMT.M76.OriginalProperDiskTriangulation
