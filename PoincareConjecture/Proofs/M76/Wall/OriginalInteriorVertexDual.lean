import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorStarBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualVertexFaceContainment
import PoincareConjecture.Proofs.M76.Mathlib.SubdivisionVertices

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem isFinitePLBallPair_original_interior_vertex_dual
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (hpR : (g p : X) ∈ interior R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z))) :
    IsFinitePLBallPair V3 (K.barycentricDualBlock {p}).space
      ((K.barycentricDualBlock {p}).link p).space := by
  let J := K.barycentricSubdivision
  have hJs : J.space = K.space := K.barycentricSubdivision_isSubdivision.space_eq
  let H' : R ≃ₜ J.space := H.trans (Homeomorph.setCongr hJs.symm)
  have hg' (z : J.space) : (g z : X) = (H'.symm z : X) :=
    hg ⟨z, hJs.subset z.property⟩
  have hpJ : p ∈ J.vertices := K.barycentricSubdivision_isSubdivision.vertices_subset hp
  have hdual : K.barycentricDualBlock {p} = J.closedStar p :=
    K.barycentricDualBlock_singleton_eq_closedStar hp
  have hsource' : MapsTo (fun z => (g z : X)) (J.closedStar p).space B.source := by
    rw [← hdual]
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := K.exists_original_star_face_of_vertex_dual_face hp hs
    exact hsource ((K.closedStar p).convexHull_subset_space ht (hst hzs))
  have hface' : (J.closedStar p).AffineOnFaces (fun z => B (g z)) := by
    rw [← hdual]
    intro s hs
    obtain ⟨t, ht, hst⟩ := K.exists_original_star_face_of_vertex_dual_face hp hs
    obtain ⟨a, ha⟩ := hface t ht
    exact ⟨a, fun _ hx => ha (hst hx)⟩
  have hball := isFinitePLBallPair_original_interior_star J
    K.barycentricSubdivision_finite H' g hg' hpJ hpR B hsource' hface'
  rwa [← hdual] at hball

end PoincareConjecture.M76
