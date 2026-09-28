import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBaseFaces
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetBoundary

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

theorem HamiltonProperDiskTriangulation.disk_subset_region
    (T : HamiltonProperDiskTriangulation R D b) : D ⊆ R := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp (T.disk_space.symm.subset hx)
  obtain ⟨p, hps⟩ := T.disk.nonempty_of_mem_faces hs
  let pD : T.disk.vertices := ⟨p, T.disk.face_subset_vertices hs hps⟩
  have hsstar : s ∈ (T.ambient.closedStar p).faces :=
    ⟨T.disk_le hs, by simpa only [Finset.insert_eq_of_mem hps] using T.disk_le hs⟩
  have hxH := T.star_source pD ((T.ambient.closedStar p).convexHull_subset_space hsstar hxs)
  rcases (T.pairChart pD).model with ⟨hinside, _⟩ | ⟨hregion, hdisk⟩
  · exact interior_subset (hinside hxH)
  · exact (hregion x hxH).mpr ((hdisk x hxH).mp hx).1

variable [FiniteDimensional ℝ E]

theorem HamiltonProperDiskTriangulation.exists_triangle_normal_interval
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hscard : s.card = 3) :
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
  have hR : convexHull ℝ (s : Set E) ⊆ R :=
    (T.disk.convexHull_subset_space hs).trans (T.disk_space.subset.trans T.disk_subset_region)
  obtain ⟨x, hxs⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
    (Finset.coe_nonempty.mpr (T.disk.nonempty_of_mem_faces hs)).convexHull
  have hxint := T.region_interior (hR (intrinsicInterior_subset hxs))
  have hsc : s.card = Module.finrank ℝ E := hscard.trans h3.symm
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu⟩ :=
    T.ambient.hasTwoFullCofaces_of_mem_interior T.finite (T.disk_le hs) hsc hxs hxint
  have htc' : t.card = 4 := by simpa only [h3] using htc
  have huc' : u.card = 4 := by simpa only [h3] using huc
  have hcofaces : ∀ v ∈ T.ambient.faces, s ⊆ v → v.card = 4 → v = t ∨ v = u := by
    intro v hv hsv hvc
    exact T.ambient.full_coface_eq_of_paired_facet hsc ht hu hv htc huc
      (by simpa only [h3] using hvc) hst hsu hsv htu hxs
  have hbound : ∀ v ∈ T.ambient.faces, v.card ≤ 3 + 1 := by
    intro v hv
    have h := (T.ambient.indep hv).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe, h3] using h
  have hpair := T.ambient.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    hbound (T.disk_le hs) ht hu hscard htc' huc' hst hsu htu hcofaces
  refine ⟨t, ht, u, hu, hst, hsu, htc', huc', htu, hcofaces, hpair.1, hpair.2, ?_⟩
  exact T.ambient.barycentricDualBlock_link_space_of_paired_facet
    hbound (T.disk_le hs) ht hu hscard htc' huc' hst hsu hcofaces

end PoincareConjecture.M76.HamiltonIndexOne
