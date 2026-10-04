import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalFrontierStars
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.Mathlib.EmbeddedStarCofaces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.Mathlib.EmbeddedFaceDimension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.Mathlib.CompleteCofaceDualBlock

/-!
# Entire original boundary dual intervals at disk edges

The genuine planar chart bounds faces only in its actual boundary
star. That star retains every coface of the edge, hence its entire
dual complex is the original boundary dual.
See Hudson1969, pp.8--9,58--63 and rigidity023, section2.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

/-- Two whole original boundary triangles, with their exhaustive
classification, come from the actual planar boundary-star image.
See rigidity023, section2. -/
theorem exists_frontier_edge_triangle_cofaces
    {s : Finset (T.index → ℝ × V3)} (hsD : s ∈ (T.marked 2).faces)
    (hsB : s ∈ (T.marked 1).faces) (hscard : s.card = 2) :
    ∃ t ∈ (T.marked 1).faces, ∃ v ∈ (T.marked 1).faces,
      s ⊆ t ∧ s ⊆ v ∧ t.card = 3 ∧ v.card = 3 ∧ t ≠ v ∧
      ∀ u ∈ (T.marked 1).faces, s ⊆ u → u.card = 3 → u = t ∨ u = v := by
  classical
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hsD
  let pD : (T.marked 2).vertices := ⟨p, (T.marked 2).face_subset_vertices hsD hps⟩
  have hpB : (T.inverse p : X) ∈ frontier R :=
    (T.inverse_mem_boundary_iff (T.ambient.subset_space (T.marked_le 1 hsB) hps)).mpr
      ((T.marked 1).subset_space hsB hps)
  obtain ⟨f, hf, hi, hint, _⟩ := T.exists_frontier_star_plane_chart pD hpB
  have hcard : s.card = Module.finrank ℝ P2 := by simpa [Module.finrank_prod] using hscard
  simpa only [Module.finrank_prod, Module.finrank_self] using
    (T.marked 1).exists_paired_facet_of_embedded_star (T.marked_finite 1)
      hsB hcard hps f hf hi hint

open Classical in
/-- The same original boundary edge dual is an entire finite PL
interval with both original triangle centroids as its exact link.
No global dimension bound for the old boundary mark is assumed.
See rigidity023, section2. -/
theorem exists_frontier_edge_dual_interval
    {s : Finset (T.index → ℝ × V3)} (hsD : s ∈ (T.marked 2).faces)
    (hsB : s ∈ (T.marked 1).faces) (hscard : s.card = 2) :
    let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
    ∃ t ∈ (T.marked 1).faces, ∃ v ∈ (T.marked 1).faces,
      s ⊆ t ∧ s ⊆ v ∧ t.card = 3 ∧ v.card = 3 ∧ t ≠ v ∧
      IsFinitePLBallPair ℝ ((T.marked 1).barycentricDualBlock s).space
        {t.centroid ℝ id, v.centroid ℝ id} ∧
      (((T.marked 1).barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, v.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hsD
  let pD : (T.marked 2).vertices := ⟨p, (T.marked 2).face_subset_vertices hsD hps⟩
  have hpB : (T.inverse p : X) ∈ frontier R :=
    (T.inverse_mem_boundary_iff (T.ambient.subset_space (T.marked_le 1 hsB) hps)).mpr
      ((T.marked 1).subset_space hsB hps)
  obtain ⟨f, hf, hi, _, _⟩ := T.exists_frontier_star_plane_chart pD hpB
  let S := (T.marked 1).closedStar p
  let : Fintype S.faces :=
    (SimplicialComplex.finite_closedStar_faces (T.marked_finite 1) p).fintype
  have hbound : ∀ u ∈ S.faces, u.card ≤ 2 + 1 := by
    intro u hu
    simpa only [Module.finrank_prod, Module.finrank_self] using
      hf.face_card_le_of_injOn hi hu
  have hcoface {u : Finset (T.index → ℝ × V3)}
      (hu : u ∈ (T.marked 1).faces) (hsu : s ⊆ u) : u ∈ S.faces :=
    ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hps)] using hu⟩
  have hdual : S.barycentricDualBlock s = (T.marked 1).barycentricDualBlock s :=
    (T.marked 1).barycentricDualBlock_eq_of_cofaces_in_subcomplex S
      (fun _ hu => hu.1) s (fun _ hu hsu => hcoface hu hsu)
  obtain ⟨t, ht, v, hv, hst, hsv, htc, hvc, htv, hexhaust⟩ :=
    T.exists_frontier_edge_triangle_cofaces hsD hsB hscard
  have hpair := S.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    hbound (hcoface hsB Subset.rfl) (hcoface ht hst) (hcoface hv hsv)
    hscard htc hvc hst hsv htv (fun u hu hsu huc => hexhaust u hu.1 hsu huc)
  have hlink := S.barycentricDualBlock_link_space_of_paired_facet
    hbound (hcoface hsB Subset.rfl) (hcoface ht hst) (hcoface hv hsv)
    hscard htc hvc hst hsv (fun u hu hsu huc => hexhaust u hu.1 hsu huc)
  rw [hdual] at hpair hlink
  exact ⟨t, ht, v, hv, hst, hsv, htc, hvc, htv, hpair.1, hlink⟩

end PoincareMT.M76.OriginalProperDiskTriangulation
