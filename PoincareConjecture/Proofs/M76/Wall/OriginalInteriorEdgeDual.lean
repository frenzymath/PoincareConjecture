import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.OriginalDiskStarNeighborhood
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarEdgeLink
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolygonLinkDualDisk

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem isFinitePLBallPair_original_interior_edge_dual
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 2)
    {p : E} (hps : p ∈ s) (hpR : (g p : X) ∈ interior R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z))) :
    IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  have hp : p ∈ K.vertices := K.face_subset_vertices hs hps
  obtain ⟨hi, _, hint⟩ := K.exists_original_open_neighborhood_inside_closedStar
    (Set.toFinite K.faces) H g hg hp hpR B hsource
  obtain ⟨n, P, hPi, hP, hPs⟩ := K.exists_polygon_faceLink_of_embedded_star
    (Set.toFinite K.faces) (F := V3) (by simp) hs hcard hps
    (fun z => B (g z)) hface hi hint
  exact K.isFinitePLBallPair_dualBlock_of_polygon_faceLink hs P hPi hP hPs

end PoincareConjecture.M76
