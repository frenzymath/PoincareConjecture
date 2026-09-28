import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon

set_option autoImplicit false

open Set

namespace Polygon

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {n : ℕ}

def affineImage (P : Polygon E n) (f : E →ᵃ[ℝ] F) : Polygon F n := ⟨f ∘ P⟩

theorem affineImage_edgeSet (P : Polygon E n) (f : E →ᵃ[ℝ] F) (i : Fin n) :
    (P.affineImage f).edgeSet ℝ i = f '' P.edgeSet ℝ i :=
  (affineSegment_image f _ _).symm

theorem affineImage_edgeVertices (P : Polygon E n) (f : E →ᵃ[ℝ] F) (i : Fin n) :
    ((P.affineImage f).edgeVertices i : Set F) = f '' (P.edgeVertices i : Set E) := by
  classical
  simp [edgeVertices, affineImage, Function.comp_def, image_pair]

theorem affineImage_boundary (P : Polygon E n) (f : E →ᵃ[ℝ] F) :
    (P.affineImage f).boundary ℝ = f '' P.boundary ℝ := by
  simp only [boundary, affineImage_edgeSet, image_iUnion]

theorem hasSimplicialEdges_affineImage (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) :
    (P.affineImage f).HasSimplicialEdges := by
  intro i j
  rw [P.affineImage_edgeSet, P.affineImage_edgeSet, ← image_inter hf,
    P.affineImage_edgeVertices, P.affineImage_edgeVertices, ← image_inter hf,
    ← f.image_convexHull]
  exact image_mono (hP i j)

end Polygon
