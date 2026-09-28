import PoincareConjecture.Proofs.M76.Mathlib.OriginalPolygonEventBodies
import PoincareConjecture.Proofs.M76.Mathlib.CenteredOriginalConnectorBody










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



noncomputable def sphereCollarCenter (q : E) : E ≃ᴬ[ℝ] E :=
  ContinuousAffineEquiv.constVAdd ℝ E (-q)



noncomputable def sphereCollarOriginal (K : SimplicialComplex ℝ E) (q : E) :
    SimplicialComplex ℝ E :=
  (K.affineOnFaces_affine (sphereCollarCenter q).toContinuousAffineMap).embeddedImage
    (sphereCollarCenter q).injective.injOn




structure SphereCollarBody (K : SimplicialComplex ℝ E) (q : E) where
  auxiliary : SimplicialComplex ℝ E
  carrier : Set E
  halfspaces : Finset (E →ₗ[ℝ] ℝ)
  frontierComplex : SimplicialComplex ℝ E
  original_finite : (sphereCollarOriginal K q).faces.Finite
  original_space : (sphereCollarOriginal K q).space = sphereCollarCenter q '' K.space
  original_bound : ∀ s ∈ (sphereCollarOriginal K q).faces, s.card ≤ 3
  auxiliary_finite : auxiliary.faces.Finite
  auxiliary_space : auxiliary.space = (sphereCollarOriginal K q).space
  zero_vertex : (0 : E) ∈ auxiliary.vertices
  pure : ∀ s ∈ auxiliary.faces, ∃ t ∈ auxiliary.faces, t.card = 3 ∧ s ⊆ t
  cofaces : ∀ s ∈ auxiliary.faces, s.card = 2 →
    {t : Finset E | t ∈ auxiliary.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2
  connected_link : (auxiliary.link 0).vertexAbstractComplex.edgeGraph.Connected
  compact : IsCompact carrier
  convex : Convex ℝ carrier
  zero_interior : (0 : E) ∈ interior carrier
  disjoint_link : Disjoint carrier (auxiliary.link 0).space
  local_star : auxiliary.space ∩ carrier = (auxiliary.closedStar 0).space ∩ carrier
  original_incidence : ∀ s ∈ (sphereCollarOriginal K q).faces,
    (convexHull ℝ (s : Set E) ∩ carrier).Nonempty →
      (0 : E) ∈ convexHull ℝ (s : Set E)
  halfspaces_nonempty : halfspaces.Nonempty
  halfspaces_nonzero : ∀ A ∈ halfspaces, A ≠ 0
  halfspaces_carrier : carrier = {x | ∀ A ∈ halfspaces, A x ≤ 1}
  frontier_finite : frontierComplex.faces.Finite
  frontier_space : frontierComplex.space = frontier carrier

end PoincareConjecture.M76.ZeroChargeJoint
