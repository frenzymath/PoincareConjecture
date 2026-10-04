import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Affine.ConvexSpherePolygonCut
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.NestedPLBallRelativeInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.AlexanderComplexityOrdinaryDiskBoundary

/-!
# The actual complement of a disk on a convex two-sphere

A pole-avoiding large disk chart supplies the given disk's
exact sphere-relative interior. The checked polygon cut then
gives its entire complementary disk with the same actual rim.
See Alexander 1924, p. 7 and M76 derivation 248f.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite PL disk on a finite convex two-sphere has its
specified rim complement as exact relative interior whenever
an actual sphere point lies outside it. See M76 derivation 248f. -/
theorem interior_preimage_convex_sphere_disk (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hspace : K.space = frontier C)
    (hdim : Module.finrank ℝ E = 3) {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hdC : d ⊆ frontier C)
    (hout : (frontier C \ d).Nonempty) :
    interior ((Subtype.val : frontier C → E) ⁻¹' d) =
      (Subtype.val : frontier C → E) ⁻¹' (d \ q) := by
  obtain ⟨p, hpC, hpd⟩ := hout
  obtain ⟨G, r, hG, hGC, hdG, _, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK hC hcv hne hspace
      (F := ℝ × ℝ) (by simpa [Module.finrank_prod] using hdim)
      ⟨p, hpC⟩ hd.isCompact hdC hpd
  have hint := hG.interior_preimage_subball hd hdG
  exact interior_preimage_val_of_open_neighborhood hGC (hdG.trans sdiff_subset)
    sdiff_subset hopen (sdiff_subset.trans hdG) sdiff_subset hint

/-- The complete complementary region of an actual finite PL
disk on a convex two-sphere is another finite PL disk with
the same entire rim. The outside-point premise is retained.
See Alexander p. 7 and M76 derivation 248f. -/
theorem isFinitePLBallPair_convex_sphere_disk_complement (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hspace : K.space = frontier C)
    (hdim : Module.finrank ℝ E = 3) {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hdC : d ⊆ frontier C)
    (hout : (frontier C \ d).Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) (frontier C \ (d \ q)) q := by
  have hint := K.interior_preimage_convex_sphere_disk hK hC hcv hne hspace hdim hd hdC hout
  obtain ⟨n, P, hPi, hPe, hPq⟩ := hd.exists_polygon_boundary
  have hdP : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) := by rwa [hPq]
  have hintP : interior ((Subtype.val : frontier C → E) ⁻¹' d) =
      (Subtype.val : frontier C → E) ⁻¹' (d \ P.boundary ℝ) := by rwa [hPq]
  have h := K.isFinitePLBallPair_convex_sphere_complement hK hC hcv hne hspace hdim
    P hPe hPi hdP hdC hintP hout
  rwa [hPq] at h

end Geometry.SimplicialComplex
