import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Affine.ConvexSphereLargeDisks
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonPLSubdisk
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallTopology

/-!
# Polygon disks on finite PL convex two-spheres

A large disk chart avoiding a chosen pole contains the whole
polygon. Fill it in the planar chart and return by the inverse
PL map. See Alexander 1924, p. 7, Hudson 1969, pp. 15--19 and
M76 derivation 139.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The polygon surface disk has its full rim complement as
its exact interior in the sphere. See Alexander p. 7 and
M76 derivations 139--140. -/
theorem exists_convex_sphere_polygon_disk_with_interior (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ frontier s) (p : frontier s)
    (hp : (p : E) ∉ P.boundary ℝ) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      D ⊆ frontier s ∧ (p : E) ∉ D ∧
      interior ((Subtype.val : frontier s → E) ⁻¹' D) =
        (Subtype.val : frontier s → E) ⁻¹' (D \ P.boundary ℝ) := by
  obtain ⟨d, q, hd, hds, hPd, hpd, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK hs hcv
      hne hspace (F := ℝ × ℝ) (by simpa [Module.finrank_prod] using hdim)
      p P.isCompact_boundary hPsub hp
  obtain ⟨D, hD, hDd, hint⟩ := hd.exists_polygon_subdisk_with_interior P hP hinj hPd
  refine ⟨D, hD, hDd.trans (sdiff_subset.trans hds), fun hx => hpd (hDd hx).1, ?_⟩
  exact interior_preimage_val_of_open_neighborhood hds (hDd.trans sdiff_subset)
    sdiff_subset hopen (sdiff_subset.trans hDd) sdiff_subset hint

/-- A simple polygon on a finite triangulated convex two-sphere
bounds a finite PL surface disk avoiding any chosen pole outside
the polygon. The disk boundary is exactly the polygon.
See Alexander p. 7 and M76 derivation 139. -/
theorem exists_convex_sphere_polygon_disk (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ frontier s) (p : frontier s)
    (hp : (p : E) ∉ P.boundary ℝ) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      D ⊆ frontier s ∧ (p : E) ∉ D := by
  obtain ⟨D, hD, hDs, hpD, _⟩ := K.exists_convex_sphere_polygon_disk_with_interior
    hK hs hcv hne hspace hdim P hP hinj hPsub p hp
  exact ⟨D, hD, hDs, hpD⟩

end Geometry.SimplicialComplex
