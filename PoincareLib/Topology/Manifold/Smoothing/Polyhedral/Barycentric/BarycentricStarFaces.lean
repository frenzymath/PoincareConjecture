import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedStarFaces

/-!
# Face-chain coordinates for barycentric stars

The actual barycentric subdivision inherits the face and
original-vertex-star descriptions of positive-center derived
subdivisions. See Hudson 1969, pp. 8--9 and M76 derivation 271.
-/

set_option autoImplicit false

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- Barycentric faces are exactly the centroid images of
nonempty coarse face chains. See Hudson pp. 8--9 and M76
derivation 271. -/
theorem barycentricSubdivision_faces (t : Finset E) :
    t ∈ K.barycentricSubdivision.faces ↔
      ∃ a : Finset K.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        t = a.image (fun s => s.val.centroid ℝ id) := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_faces _ _ t

/-- A barycentric face belongs to the closed star of an
original vertex exactly when every face of its coarse chain
contains that vertex. See Hudson pp. 8--9 and M76 derivation 271. -/
theorem barycentricSubdivision_closedStar_faces {p : E}
    (hp : {p} ∈ K.faces) (t : Finset E) :
    t ∈ (K.barycentricSubdivision.closedStar p).faces ↔
      ∃ a : Finset K.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        t = a.image (fun s => s.val.centroid ℝ id) ∧ ∀ s ∈ a, p ∈ s.val := by
  unfold barycentricSubdivision
  exact K.derivedSubdivision_closedStar_faces _ _ hp t

end Geometry.SimplicialComplex
