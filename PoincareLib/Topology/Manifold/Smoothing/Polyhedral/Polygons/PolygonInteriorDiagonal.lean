import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonCornerNormalization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonEmptyTriangle
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonRegionAffineImage

/-!
# Every simple planar polygon has an interior diagonal

A strict extreme corner provides normalized supporting coordinates.
The normalized diagonal construction and affine region transport
then give a diagonal without coordinate restrictions. See Erickson,
Simple Polygons, Section 1.4, pp. 7--8 and M76 derivation 111.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- A simple planar polygon with at least four distinct cyclic
vertices admits a segment between distinct nonadjacent vertices
whose open segment lies inside. Collinear vertices are permitted.
See Erickson pp. 7--8 and M76 derivation 111. -/
theorem exists_interior_diagonal {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 4))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ a b : Fin (n + 4), a ≠ b ∧ b ≠ finRotate (n + 4) a ∧
      a ≠ finRotate (n + 4) b ∧ openSegment ℝ (P a) (P b) ⊆ P.inside := by
  obtain ⟨i, e, L, hp, hi, hn, hL, hd⟩ := P.exists_supported_axis_corner hP hinj
  let Q := P.affineImage e.toAffineEquiv.toAffineMap
  have hQ : Q.HasSimplicialEdges :=
    P.hasSimplicialEdges_affineImage hP _ e.injective
  have hQinj : Function.Injective Q := e.injective.comp hinj
  obtain ⟨a, b, hab, hba, hab', hseg⟩ :=
    Q.exists_diagonal_of_normalized_corner hQ hQinj i hp hi hn L hL hd
  refine ⟨a, b, hab, hba, hab', ?_⟩
  intro x hx
  apply (P.mem_inside_affineImage_iff e x).mp
  apply hseg
  change e x ∈ openSegment ℝ (e.toAffineEquiv.toAffineMap (P a))
    (e.toAffineEquiv.toAffineMap (P b))
  have himage := image_openSegment ℝ e.toAffineEquiv.toAffineMap (P a) (P b)
  rw [← himage]
  exact mem_image_of_mem _ hx

end Polygon
