import PoincareLib.Topology.Plane.Meshes.Subdivision.Lines

/-!
# Rescaling affine mesh cuts

Metric sector boundaries can use any nonzero rescaling of the retained
topological cuts. The actual triangle side partition is unchanged.
-/

set_option autoImplicit false

open Poincare.Topology.Plane.Meshes

namespace PoincareMT.Topology.Surface

/-- Scalar multiplication preserves the actual monochromatic side partition. -/
theorem isMonochromatic_smul (N : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (hN : N.IsMonochromatic f) (r : ℝ) : N.IsMonochromatic (r • f) := by
  intro t ht
  rcases hN t ht with hp | hn
  · rcases le_total 0 r with hr | hr
    · exact Or.inl (fun v hv => mul_nonneg hr (hp v hv))
    · exact Or.inr (fun v hv => mul_nonpos_of_nonpos_of_nonneg hr (hp v hv))
  · rcases le_total 0 r with hr | hr
    · exact Or.inr (fun v hv => mul_nonpos_of_nonneg_of_nonpos hr (hn v hv))
    · exact Or.inl (fun v hv => mul_nonneg_of_nonpos_of_nonpos hr (hn v hv))

end PoincareMT.Topology.Surface
