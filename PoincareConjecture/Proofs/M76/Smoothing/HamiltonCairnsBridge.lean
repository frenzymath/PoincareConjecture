import PoincareConjecture.Proofs.M76.Smoothing.FiniteTriangulationBridge
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonAffineStars
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarPurity
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarConnectedLinks












set_option autoImplicit false

open Set Geometry

universe u

namespace PoincareConjecture.M76

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]






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

end PoincareConjecture.M76
