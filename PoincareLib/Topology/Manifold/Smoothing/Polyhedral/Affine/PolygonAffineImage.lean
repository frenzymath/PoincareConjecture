import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialPolygon

/-!
# Affine images of polygon boundaries

Affine maps carry polygon boundaries to the corresponding
boundary. Injectivity preserves the simplicial edge-intersection
law. See Erickson, Simple Polygons, pp. 2--4 and M76 derivation 99.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {n : ℕ}

/-- Apply one affine map to every labelled polygon vertex.
See M76 derivation 99. -/
def affineImage (P : Polygon E n) (f : E →ᵃ[ℝ] F) : Polygon F n := ⟨f ∘ P⟩

/-- An image polygon's edge is the image of its source edge.
See Erickson pp. 2--4 and M76 derivation 99. -/
theorem affineImage_edgeSet (P : Polygon E n) (f : E →ᵃ[ℝ] F) (i : Fin n) :
    (P.affineImage f).edgeSet ℝ i = f '' P.edgeSet ℝ i :=
  (affineSegment_image f _ _).symm

/-- The endpoint set of an image edge is the affine image of
the endpoint set. See M76 derivation 99. -/
theorem affineImage_edgeVertices (P : Polygon E n) (f : E →ᵃ[ℝ] F) (i : Fin n) :
    ((P.affineImage f).edgeVertices i : Set F) = f '' (P.edgeVertices i : Set E) := by
  classical
  simp [edgeVertices, affineImage, Function.comp_def, image_pair]

/-- The boundary of the image polygon equals the image of the
whole boundary, even for noninjective maps. See M76 derivation 99. -/
theorem affineImage_boundary (P : Polygon E n) (f : E →ᵃ[ℝ] F) :
    (P.affineImage f).boundary ℝ = f '' P.boundary ℝ := by
  simp only [boundary, affineImage_edgeSet, image_iUnion]

/-- Injective affine maps preserve the simplicial edge-intersection
law of a polygon. See Erickson pp. 2--4 and M76 derivation 99. -/
theorem hasSimplicialEdges_affineImage (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) :
    (P.affineImage f).HasSimplicialEdges := by
  intro i j
  rw [P.affineImage_edgeSet, P.affineImage_edgeSet, ← image_inter hf,
    P.affineImage_edgeVertices, P.affineImage_edgeVertices, ← image_inter hf,
    ← f.image_convexHull]
  exact image_mono (hP i j)

end Polygon
