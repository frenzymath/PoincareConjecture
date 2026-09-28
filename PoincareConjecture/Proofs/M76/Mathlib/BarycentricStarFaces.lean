import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarFaces

set_option autoImplicit false

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem barycentricSubdivision_faces (t : Finset E) :
    t ∈ K.barycentricSubdivision.faces ↔
      ∃ a : Finset K.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        t = a.image (fun s => s.val.centroid ℝ id) := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_faces _ _ t

theorem barycentricSubdivision_closedStar_faces {p : E}
    (hp : {p} ∈ K.faces) (t : Finset E) :
    t ∈ (K.barycentricSubdivision.closedStar p).faces ↔
      ∃ a : Finset K.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        t = a.image (fun s => s.val.centroid ℝ id) ∧ ∀ s ∈ a, p ∈ s.val := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_closedStar_faces _ _ hp t

end Geometry.SimplicialComplex
