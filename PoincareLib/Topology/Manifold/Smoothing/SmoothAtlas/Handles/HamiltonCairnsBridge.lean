import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.General.FiniteTriangulationBridge
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.HamiltonAffineStars
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineStarPurity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineStarConnectedLinks

/-!
# From supported Hamilton straightening to the Cairns smoothing bridge

The actual compact graph embedding supplies a finite geometric
triangulation with affine Brouwer stars. Their local geometry
gives purity and the closed link conditions, so the existing
Cairns construction applies. The local Hamilton straightening
supplier remains an explicit input. See Hamilton 1976, p. 69,
Cairns 1940, pp. 798--800, 806--807 and M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry

universe u

namespace PoincareMT.M76

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- Supported local Hamilton overlap straightening supplies
the frozen smoothing conclusion by an actual finite geometric
triangulation and the checked Cairns construction. The local
straightening supplier is retained as a hypothesis. See
Hamilton p. 69, Cairns pp. 806--807 and M76 derivation 258. -/
theorem smoothingConclusion_of_supportedPLOverlapStraightening
    (P : SmoothingBridgeInput (M := M))
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := EuclideanSpace ℝ (Fin 3))) :
    M76SmoothingConclusion P := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨s, K, hK, hstars, ⟨e⟩⟩ :=
    ChartedSpace.exists_finite_geometric_affine_star_triangulation hlocal
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine smoothingConclusion_of_finite_geometric_triangulation P K hK ?_ ?_ ?_ ?_ e
  · simpa only [hdim] using K.exists_full_coface_of_affine_vertex_stars hK hstars
  · intro t ht htcard
    apply K.isConnected_faceLink_of_affine_vertex_stars hK hstars t ht
    rw [htcard, hdim]
    norm_num
  · intro t ht htcard
    apply K.faceLink_ncard_eq_two_of_affine_vertex_stars hK hstars t ht
    exact htcard.trans hdim.symm
  · intro p hp
    obtain ⟨a, hinj, hint⟩ := hstars p hp
    exact ⟨a, (K.closedFaceStar {p}).affineOnFaces_affine a, hinj, ⟨a p, hint⟩⟩

end PoincareMT.M76
