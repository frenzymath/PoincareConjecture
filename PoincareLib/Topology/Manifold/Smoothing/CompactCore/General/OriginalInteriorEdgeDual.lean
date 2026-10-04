import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.Mathlib.OriginalDiskStarNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.EmbeddedStarEdgeLink
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.Mathlib.PolygonLinkDualDisk

/-!
# Actual joint disks from original interior edge endpoints

An original interior endpoint gives a genuine open neighborhood in
the containing star's three-dimensional chart image. Its full original
edge link is therefore a polygon, producing the literal dual disk
with its entire centroid link as rim. See Wall013, section 4,
Hudson 1969, pp. 8--10, 58--63.
-/

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- An actual edge with an original interior endpoint and a chart
on that endpoint's entire star has its literal barycentric dual
disk with the whole centroid link as rim. Only the actual chart
target has dimension three. See Wall013, section 4. -/
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

end PoincareMT.M76
