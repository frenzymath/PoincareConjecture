import PoincareLib.Topology.Manifold.Schoenflies.Plane.Rounding.Ambient
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Rounding.Reduction

/-!
# Smooth planar circle normalization

An arbitrary smooth embedded circle is transported to a coherently rounded
simple polygon in its normal annulus. Admissible vertex pushes and smooth
midpoint deletions reduce that polygon to a triangle. Composing the inverse
of these ambient maps with the rounded-triangle normalization constructs a
global smooth diffeomorphism taking the unit circle to the supplied image.

This proves the ambient form of the smooth planar disk theorem used in
Hatcher, Notes on Basic 3-Manifold Topology (2014), Theorem 1.1, printed p. 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2) := ⟨by simp⟩

/-- Every smooth embedded planar circle is the image of the unit circle
under a smooth diffeomorphism of the whole plane. -/
theorem exists_ambient_diffeomorph_of_smooth_circle
    (f : sphere (0 : EuclideanSpace Real (Fin 2)) 1 -> EuclideanSpace Real (Fin 2))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
      F '' sphere (0 : EuclideanSpace Real (Fin 2)) 1 = range f := by
  let e := Complex.orthonormalBasisOneI.repr
  let o := Orientation.map (Fin 2) e.toLinearEquiv Complex.orientation
  obtain ⟨n, p, hp, happrox⟩ := Plane.exists_ambient_rounded_polygon_of_smooth_circle e o f hf
  obtain ⟨d, hd, hdsmall, hnormalize⟩ :=
    Plane.exists_uniform_ambient_diffeomorph_rounded_polygon e o p hp
  obtain ⟨δ, hδ, hδd⟩ := exists_between hd
  obtain ⟨ρ, hρ, _, _, htail, hbound, hder⟩ := Plane.exists_smooth_absolute_rounding hδ
  obtain ⟨A, _, hA⟩ := happrox δ hδ (hδd.trans hdsmall) ρ hρ htail hbound hder
  obtain ⟨B, hB⟩ := hnormalize δ hδ hδd ρ hρ htail hbound hder
  refine ⟨B.trans A.symm, ?_⟩
  change (fun x => A.symm (B x)) '' sphere (0 : EuclideanSpace Real (Fin 2)) 1 = range f
  rw [← image_image A.symm B, hB, ← hA]
  exact A.toEquiv.symm_image_image _

end Poincare.Manifold.Schoenflies
